/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortInputMode.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
/-!
# Valid top-level listsort inputs

The raw transcription keeps `hasKeyfunc` separate from its paired-entry input,
just as the C function keeps a nullable values pointer separate from the keys
pointer.  This module provides the public proof-carrying boundary: callers can
construct only inputs whose entries agree with that mode, while execution
still delegates unchanged to `listSortImpl?`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- A top-level input whose paired entries agree with the explicit key-function
mode passed to `listSortImpl?`. -/
structure ListSortInput (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  hasKeyfunc : Bool
  valuesMode : SortSlice.ValuesModeInvariant hasKeyfunc slice

end CPythonListsort
