/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean -/

import Inductive.CPythonListsort.Code.Assembly.MergeTreeCost
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Tactic
import Theorem.CPythonListsort.Code.Assembly.MergePolicyReplay
/-!
# Checked replay of the interleaved PowerSort policy trace

The access trace records formed-run pushes and logical, pre-trimming merges in
one chronological channel.  This module gives that raw channel a deliberately
strict, pure semantics.  A formed-run observation is accepted only when its
post-push depth, source interval, adaptive-minrun branch, and remaining-input
metadata agree.  A merge is accepted only when its index and full source
spans identify an adjacent pair in the current forest.

Every replayed internal node is labelled by the transcribed `powerloop`
applied to the aggregate spans being merged.  No label supplied by the trace
is trusted, and physical trimming does not alter the logical merge cost.
-/

/-! ## Raw event projections -/


namespace CPythonListsort

namespace PolicyEvent

/-! ## Empty/single-root normalization -/

/-- Normalize a completed forest to the paper-facing empty-or-tree plan.

The empty forest is accepted only for an empty input.  A singleton is accepted
only when its root span is exactly the declared input span. -/
def normalizePolicyForest? (input : RunSpan) :
    List SpannedMergeTree → Option MergePlan
  | [] => if input.len = 0 then some .empty else none
  | [root] => if root.span = input then some (.tree root.tree) else none
  | _ => none

/-- Replay and normalize one complete policy trace. -/
def replayMergePlan? (input : RunSpan)
    (events : List PolicyEvent) : Option MergePlan := do
  let forest ← replayPolicyEvents? input events
  normalizePolicyForest? input forest

end PolicyEvent
end CPythonListsort
