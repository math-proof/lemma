/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectnessSupport
import Def.CPythonListsort.Code.Correctness.MergeHiCorrectness
import Structure.CPythonListsort.Code.Correctness.MergeLoCorrectness
import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeTopPowerPreservation
/-!
# Functional correctness of `merge_at`

This module lifts the exact trimmed-range specifications of `merge_lo` and
`merge_hi` to the complete adjacent pair selected by `merge_at`.  Its public
postcondition is deliberately phrased at the scan invariant boundary: the
actual traced evaluator succeeds, the selected union is the mathematical
left-biased stable merge, all pending runs remain correct, the persistent
whole-entry snapshot is preserved, and no entry outside the consumed prefix
changes.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Whole entries of the left run selected by `merge_at`, before trimming. -/
def mergeAtLeftEntries (pre : MergeState (Occurrence alpha) nu)
    (left : PendingRun) : List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries pre.data left.base left.len.toNat).toList

/-- Whole entries of the right run selected by `merge_at`, before trimming. -/
def mergeAtRightEntries (pre : MergeState (Occurrence alpha) nu)
    (right : PendingRun) : List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries pre.data right.base right.len.toNat).toList

/-- The source-faithful full-union target: an ordinary forward, left-biased
stable merge of the two complete adjacent runs. -/
def mergeAtTargetEntries (lt : BoolComparator alpha)
    (pre : MergeState (Occurrence alpha) nu) (left right : PendingRun) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  stableEntryMerge lt (mergeAtLeftEntries pre left)
    (mergeAtRightEntries pre right)

end CPythonListsort
