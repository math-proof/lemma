/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean -/

import Def.CPythonListsort.Code.Transcription.TempStorageInvariant
/-!
# `merge_init` temporary-storage initialization

This is the storage projection of CPython's `merge_init`.  Fresh modeled cells
are uninitialized (`none`).  In keyed mode each logical entry consumes two raw
pointer slots from the 256-slot inline buffer; in unkeyed mode it consumes one.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable temporary-storage fields initialized by `merge_init`. -/
structure MergeInitTempResult (κ : Type u) (ν : Type v) where
  storage : TempStorage κ ν
  alloced : PySSize
  deriving DecidableEq, Repr

end CPythonListsort
