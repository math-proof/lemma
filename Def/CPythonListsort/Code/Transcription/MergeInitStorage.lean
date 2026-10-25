/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
import Structure.CPythonListsort.Code.Transcription.MergeInitStorage
/-!
# `merge_init` temporary-storage initialization

This is the storage projection of CPython's `merge_init`.  Fresh modeled cells
are uninitialized (`none`).  In keyed mode each logical entry consumes two raw
pointer slots from the 256-slot inline buffer; in unkeyed mode it consumes one.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Inline capacity selected by the storage part of `merge_init`, retaining the
signed 64-bit addition, division, and comparison performed by C. -/
def mergeInitTempCapacity (listSize : PySSize) (hasKeyfunc : Bool) : PySSize :=
  if hasKeyfunc then
    let requested := (listSize + 1).sdiv 2
    let inlineCap : PySSize := BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)
    if inlineCap.slt requested then inlineCap else requested
  else
    BitVec.ofNat 64 MERGESTATE_TEMP_SIZE

/-- Temporary-storage portion of pinned CPython `merge_init`. -/
def mergeInitTemp (listSize : PySSize) (hasKeyfunc : Bool) :
    MergeInitTempResult κ ν :=
  let capacity := mergeInitTempCapacity listSize hasKeyfunc
  { storage :=
      { cells := Array.replicate capacity.toNat none
        backing := .inline
        hasValues := hasKeyfunc }
    alloced := capacity }

end CPythonListsort
