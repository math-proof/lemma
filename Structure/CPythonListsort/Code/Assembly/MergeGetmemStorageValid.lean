/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
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

end CPythonListsort
