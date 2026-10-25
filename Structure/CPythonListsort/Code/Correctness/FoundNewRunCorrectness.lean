/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/FoundNewRunCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety.Part2
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness.Part2
/-!
# Functional correctness of `found_new_run`

This module carries pending-run correctness and the persistent whole-entry
snapshot through the actual `foundNewRunLoop?` collapse loop.  Pending-power
writes are proved semantically inert, while every taken merge is discharged by
`mergeAt_correct`.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Semantic state facts preserved by the collapse loop.  The frame is stated
relative to the loop call state, so recursive merge frames compose directly. -/
structure FoundNewRunSemanticPost
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (pre : MergeState (Occurrence α) ν) (scanned : Nat)
    (result : FoundNewRunResult (Occurrence α) ν) : Prop where
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- End-to-end functional certificate for one admitted `found_new_run` call. -/
structure FoundNewRunCorrectnessPost
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (pre : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun)
    (result : FoundNewRunResult (Occurrence α) ν) : Prop where
  safety : FoundNewRunSafetyPost pre scanned newRun result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

end CPythonListsort
