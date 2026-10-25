/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeCorrectness.lean -/

import Structure.CPythonListsort.Code.Correctness.ReverseScanTransport
/-!
# Correctness of CPython's reverse-mode pattern

The reverse-oriented scan transport supplies the actual pre-finish state:
sorted by the forward comparator, but reverse-stable in the original origin
labels.  This module proves that the transcribed final whole-slice reversal
turns that state into a sorted, stable result for the swapped comparator while
preserving every key/payload pair.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- The occurrence keys physically retained in a completed modeled result. -/
def ListSortImplResult.occurrences
    (result : ListSortImplResult (Occurrence alpha) nu) :
    Array (Occurrence alpha) :=
  result.state.data.entries.map SortSliceEntry.key

end CPythonListsort
