/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean -/

module

public import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
public import Def.CPythonListsort.Code.Correctness.SortSliceRange
public import Def.CPythonListsort.Code.Assembly.ListSortInputMode
public import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
public import Mathlib

@[expose] public section

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

/-! ## Whole-entry occurrence tagging -/

/-- Attach an absolute occurrence index to every key in a complete
`SortSlice`, without changing the payload paired with that key.  Tagging the
whole slice before selecting a range prevents a nonzero-base subrange from
being accidentally retagged relative to zero. -/
def tagSortSliceOccurrences (slice : SortSlice κ ν) :
    SortSlice (Occurrence κ) ν :=
  { entries := slice.entries.zipIdx.map fun entry =>
      { key := { value := entry.1.key, origin := entry.2 }
        value := entry.1.value } }

end CPythonListsort
