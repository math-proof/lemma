/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.ReverseScanTransport

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

/-- Public semantic packet for the nontrivial `reverse = true` scan branch. -/
structure ReverseModeCorrectnessPost
    (lt : BoolComparator alpha) (input : ListSortInput alpha nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  scanResultEq :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
      input.slice.entries.size true input.slice.entries.size = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  sorted : Sorted (occurrenceComparator (swappedComparator lt))
    result.occurrences
  stable : StableOccurrencePermutation (swappedComparator lt)
    (tagOccurrences
      (input.slice.entries.map SortSliceEntry.key)).toList
    result.occurrences.toList
  entrySnapshot : EntrySnapshotPermutation input.slice result.state.data
