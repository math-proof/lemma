/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean -/

import Inductive.CPythonListsort.Code.Assembly.MergeTreeCost
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Tactic
import Instance.CPythonListsort.Code.Assembly.MergePolicyReplay.Part2
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

/-- The exact transcribed node power belonging to two aggregate spans. -/
def replayBoundaryPower (input left right : RunSpan) : Nat :=
  powerloop (BitVec.ofNat 64 (left.base - input.base))
    (BitVec.ofNat 64 left.len) (BitVec.ofNat 64 right.len)
    (BitVec.ofNat 64 input.len)

/-- Apply one raw policy event to an ordered merge forest.

Formed-run metadata is checked before appending a leaf.  A merge checks both
pre-trim operand spans at the recorded index and checks adjacency before
splicing in a node labelled by `replayBoundaryPower`. -/
def applyPolicyEvent? (input : RunSpan)
    (forest : List SpannedMergeTree) :
    PolicyEvent → Option (List SpannedMergeTree)
  | .formed push =>
      if ValidFormedEvent input forest push then
        some (forest ++ [SpannedMergeTree.leaf push.run])
      else
        none
  | .merge event => do
      let left ← forest[event.index]?
      let right ← forest[event.index + 1]?
      if left.span = event.left ∧ right.span = event.right ∧
          event.left.Adjacent event.right then
        some (forest.take event.index ++
          SpannedMergeTree.merge
            (replayBoundaryPower input event.left event.right) left right ::
          forest.drop (event.index + 2))
      else
        none

/-- Replay a chronological, interleaved policy-event stream. -/
def replayPolicyEventsFrom? (input : RunSpan) :
    List SpannedMergeTree → List PolicyEvent →
      Option (List SpannedMergeTree)
  | forest, [] => some forest
  | forest, event :: events => do
      let forest ← applyPolicyEvent? input forest event
      replayPolicyEventsFrom? input forest events

/-- Replay a complete policy stream from the empty initial forest. -/
def replayPolicyEvents? (input : RunSpan)
    (events : List PolicyEvent) : Option (List SpannedMergeTree) :=
  replayPolicyEventsFrom? input [] events

end PolicyEvent
end CPythonListsort
