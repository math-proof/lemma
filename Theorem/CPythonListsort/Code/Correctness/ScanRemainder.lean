module
public import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
public import Def.CPythonListsort.Code.Correctness.SortSliceRange
public import Def.CPythonListsort.Code.Assembly.ListSortInputMode
public import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
public import Mathlib
public import Def.CPythonListsort.Code.Correctness.ScanRemainder


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean -/
/-!
# Unscanned-snapshot correctness

`PendingRunsCorrect` intentionally describes only the prefix already represented
by the pending stack.  The scan induction also needs a separate fact saying
that the still-unscanned keys are the untouched, absolutely tagged suffix of
the original snapshot.  Keeping that fact here avoids strengthening the
already-reviewed pending-run invariant.
-/
namespace CPythonListsort

universe u v

/-- Occurrence tagging preserves the input's key/payload representation mode. -/
theorem tagSortSliceOccurrences_valuesMode
    {hasKeyfunc : Bool} {slice : SortSlice κ ν}
    (h : SortSlice.ValuesModeInvariant hasKeyfunc slice) :
    SortSlice.ValuesModeInvariant hasKeyfunc (tagSortSliceOccurrences slice) := by
  intro index hindex
  have hsource : index < slice.entries.size := by simpa using hindex
  have hmode := h index hsource
  unfold SortSlice.EntryMatchesValuesMode at hmode ⊢
  split <;> simpa [tagSortSliceOccurrences] using hmode

end CPythonListsort
