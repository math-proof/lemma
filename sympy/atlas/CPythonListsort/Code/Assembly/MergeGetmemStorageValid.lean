/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.MergeMemory
import Mathlib

/-!
# `merge_getmem` storage validity

This module assembles the representation and liveness facts for the two
successful `merge_getmem` paths.  Reuse is safe only from live input storage:
the raw transcription intentionally admits a fabricated released state with a
stale `alloced`, but none of the theorems here do.  Growth uses the exact
allocation-limit premise supplied by the call-site request-bound theorem.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Certificate for the state between `merge_freemem` and successful heap
allocation on the growth path.  Inline backing is retained unchanged; live
heap backing becomes released with no accessible payload.  In both cases the
representation invariant remains true even though the heap case is
temporarily not live. -/
structure MergeGetmemIntermediateFree
    (before freed : MergeState κ ν) : Prop where
  exactState : freed = mergeFreemem before
  invariant : TempStorageInv freed.a freed.alloced
  allocedPreserved : freed.alloced = before.alloced
  valuesModePreserved : freed.a.hasValues = before.a.hasValues
  backingTransition :
    (before.a.backing = .inline ∧
        freed = before ∧
        freed.a.backing = .inline) ∨
      (before.a.backing = .heap ∧
        freed.a.backing = .released ∧
        freed.a.cells = #[])

/-- Every `MergeState` field that `merge_getmem` must frame.  Temporary
storage and its capacity are intentionally absent because growth replaces
exactly those two fields. -/
structure MergeGetmemNonStorageFrame (κ : Type u) (ν : Type v) where
  min_gallop : PySSize
  listlen : PySSize
  basekeys : Nat
  data : SortSlice κ ν
  pending : Array PendingRun
  key_compare : BoolComparator κ
  mr_current : PySSize
  mr_e : PySSize
  mr_mask : PySSize

/-- Project the non-storage frame preserved by `merge_getmem`. -/
def MergeState.mergeGetmemNonStorageFrame (state : MergeState κ ν) :
    MergeGetmemNonStorageFrame κ ν :=
  { min_gallop := state.min_gallop
    listlen := state.listlen
    basekeys := state.basekeys
    data := state.data
    pending := state.pending
    key_compare := state.key_compare
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

/-- Facts shared by both successful `merge_getmem` paths.  In particular,
`requestFits` is a natural-number capacity fact suitable for array bounds; it
is not merely a repetition of the signed branch condition. -/
structure MergeGetmemStoragePost
    (before : MergeState κ ν) (need : PySSize)
    (result : MergeGetmemResult κ ν) : Prop where
  outcome : result.outcome = .reused ∨ result.outcome = .grown
  live : result.state.a.Live
  invariant : TempStorageInv result.state.a result.state.alloced
  valuesMode : result.state.a.hasValues = before.a.hasValues
  nonStorageFrame : result.state.mergeGetmemNonStorageFrame =
    before.mergeGetmemNonStorageFrame
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : need.toNat ≤ result.state.alloced.toNat
  physicalSlots : result.state.a.physicalSlots =
    result.state.a.multiplier * result.state.alloced.toNat
  /-- Reuse is exact state preservation, not merely preservation of selected
  storage facts. -/
  reuseAccounting : result.outcome = .reused → result.state = before
  /-- A growth result exports the exact, invariant-valid intermediate state
  after freeing and before installing its fresh heap allocation. -/
  growthIntermediateFree : result.outcome = .grown →
    MergeGetmemIntermediateFree before (mergeFreemem before)
  /-- On growth, the output uses exactly the old mode's multiplier times the
  requested logical capacity, and that raw slot count passes the byte guard. -/
  growthAccounting : result.outcome = .grown →
    result.state.alloced = need ∧
      result.state.a.backing = .heap ∧
      result.state.a.multiplier = before.a.multiplier ∧
      result.state.a.physicalSlots = before.a.multiplier * need.toNat ∧
      result.state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES

namespace MergeGetmemStoragePost

variable {before : MergeState κ ν} {need : PySSize}
  {result : MergeGetmemResult κ ν}

/-! ## Regression: why live input is essential -/

/-- A concrete impossible-at-a-merge-boundary state: `alloced` remains eight,
as it can after `merge_freemem`, while the payload is empty and released. -/
def fabricatedStaleReleasedMergeState : MergeState Unit Unit :=
  { min_gallop := MIN_GALLOP
    listlen := 0
    basekeys := 0
    data := { entries := #[] }
    a :=
      { cells := #[]
        backing := .released
        hasValues := false }
    alloced := 8
    pending := #[]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }
