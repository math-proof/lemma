/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean -/

import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Assembly.ListSortInputMode
import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
import Mathlib
import Def.CPythonListsort.Code.Correctness.ScanRemainder.Part2
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

/-- Whole-entry companion to `ScanRemainderMatches`.  It says that the
unscanned suffix still contains exactly the tagged source entries, including
each optional payload, and exposes every clipping bound explicitly. -/
structure ScanRemainderEntriesMatch (source : SortSlice κ ν)
    (state : MergeState (Occurrence κ) ν) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  source_stop_le :
    state.basekeys + state.listlen.toNat ≤ source.entries.size
  entries_eq :
    (sortSliceRangeEntries state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList

/-- The unscanned state suffix is exactly the corresponding absolute-origin
segment of the original input.

The three bounds are part of the proposition rather than implicit clipping
assumptions.  The invariant has no comparator parameter: it is a snapshot and
frame property, independent of ordering laws. -/
structure ScanRemainderMatches (input : Array α)
    (state : MergeState (Occurrence α) ν) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  input_stop_le : state.basekeys + state.listlen.toNat ≤ input.size
  keys_eq :
    (sortSliceRangeKeys state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      canonicalOccurrenceSegment input (state.basekeys + scanned)
        (state.listlen.toNat - scanned)

end CPythonListsort
