/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Mathlib
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid
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

end CPythonListsort
