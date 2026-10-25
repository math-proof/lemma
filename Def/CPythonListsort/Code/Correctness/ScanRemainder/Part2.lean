/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean -/

import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Assembly.ListSortInputMode
import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
import Mathlib
import Theorem.CPythonListsort.Code.Correctness.ScanRemainder
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

namespace ListSortInput

/-- Lift a validated keyed or unkeyed input to absolute occurrence keys while
retaining every payload and the same `hasKeyfunc` mode. -/
def withOccurrenceKeys (input : ListSortInput κ ν) :
    ListSortInput (Occurrence κ) ν where
  slice := tagSortSliceOccurrences input.slice
  hasKeyfunc := input.hasKeyfunc
  valuesMode := tagSortSliceOccurrences_valuesMode input.valuesMode

end ListSortInput
end CPythonListsort
