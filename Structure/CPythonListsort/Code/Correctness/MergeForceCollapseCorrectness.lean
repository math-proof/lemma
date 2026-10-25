/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness.Part2
/-!
# Functional correctness of `merge_force_collapse`

The final collapse repeatedly delegates to the already-correct `merge_at`
implementation.  This module carries the pending-run correctness and complete
entry snapshot through the actual fuel-bounded collapse evaluator; it does not
replace that evaluator by a mathematical fold.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- End-to-end correctness at the final-collapse boundary.  Safety is embedded
verbatim so the semantic result is tied to the real composed trace. -/
structure MergeForceCollapseCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) : Prop where
  safety : MergeForceCollapseSafetyPost pre scanned result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

structure MergeForceCollapseLoopCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned fuel : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) : Prop where
  resultEq :
    (mergeForceCollapseLoopTraced? fuel pre).result = some result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

end CPythonListsort
