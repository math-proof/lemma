/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Structure.CPythonListsort.Code.Transcription.MergeMemory
/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/


namespace CPythonListsort

/-- Largest logical request whose one-or-two-slot heap allocation fits the
selected 64-bit `Py_ssize_t` allocation bound. -/
def mergeGetmemAllocationLimit (storage : TempStorage κ ν) : Nat :=
  PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / storage.multiplier

/-- Transcription of `merge_getmem` under the version-one convention that a
guard-admitted `PyMem_Malloc` call succeeds. The reuse test is signed, as in C.
The allocation guard views `need` through the same-width unsigned `size_t`
cast, represented by `need.toNat`. Fresh heap cells are uninitialized and old
payload contents are deliberately discarded rather than copied. -/
def mergeGetmem (state : MergeState κ ν) (need : PySSize) :
    MergeGetmemResult κ ν :=
  if need.sle state.alloced then
    { state := state, outcome := .reused }
  else
    let allocationLimit := mergeGetmemAllocationLimit state.a
    let freed := mergeFreemem state
    if allocationLimit < need.toNat then
      { state := freed, outcome := .guardRejected }
    else
      { state :=
          { freed with
            a :=
              { cells := Array.replicate need.toNat none
                backing := .heap
                hasValues := freed.a.hasValues }
            alloced := need }
        outcome := .grown }

end CPythonListsort
