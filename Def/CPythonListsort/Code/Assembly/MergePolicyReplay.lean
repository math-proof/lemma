/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean -/

import Inductive.CPythonListsort.Code.Assembly.MergeTreeCost
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Tactic
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

/-- The source spans of formed runs, in chronological order. -/
def formedSpans : List PolicyEvent → List RunSpan
  | [] => []
  | .formed push :: events => push.run :: formedSpans events
  | .merge _ :: events => formedSpans events

/-- The lengths of formed runs, in chronological order. -/
def formedLengths (events : List PolicyEvent) : List Nat :=
  (formedSpans events).map RunSpan.len

/-- Paper merge cost accumulated by the logical pre-trimming merge events. -/
def logicalMergeCost : List PolicyEvent → Nat
  | [] => 0
  | .formed _ :: events => logicalMergeCost events
  | .merge event :: events =>
      event.left.len + event.right.len + logicalMergeCost events

/-- The individual pre-trimming merge costs, in chronological event order.

This projection is deliberately separate from `logicalMergeCost`: executable
regressions can pin a concrete merge schedule rather than only its total. -/
def logicalMergeCosts : List PolicyEvent → List Nat
  | [] => []
  | .formed _ :: events => logicalMergeCosts events
  | .merge event :: events =>
      (event.left.len + event.right.len) :: logicalMergeCosts events

/-- Every leaf has positive length. -/
def Positive (entry : SpannedMergeTree) : Prop :=
  ∀ length ∈ entry.tree.runLengths, 0 < length

/-- Root spans in a forest are consecutive from left to right. -/
def AdjacentForest : List SpannedMergeTree → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.span.Adjacent right.span ∧ AdjacentForest (right :: rest)

/-- The first root of a nonempty forest starts at `input.base`. -/
def ForestStartsAt (input : RunSpan) : List SpannedMergeTree → Prop
  | [] => True
  | first :: _ => first.span.base = input.base

/-- Every represented interval ends within the declared input interval. -/
def ForestWithin (input : RunSpan) (forest : List SpannedMergeTree) : Prop :=
  ∀ entry ∈ forest, entry.span.endIndex ≤ input.endIndex

/-- Replay invariant: valid positive trees forming an adjacent input prefix. -/
def PolicyForestInv (input : RunSpan)
    (forest : List SpannedMergeTree) : Prop :=
  (∀ entry ∈ forest, entry.Valid ∧ entry.Positive) ∧
    AdjacentForest forest ∧
    ForestStartsAt input forest ∧
    ForestWithin input forest

/-- Flatten the leaf lengths of an ordered merge forest. -/
def forestRunLengths (forest : List SpannedMergeTree) : List Nat :=
  forest.flatMap fun entry => entry.tree.runLengths

/-- Sum the already-incurred internal merge cost of a forest. -/
def forestMergeCost (forest : List SpannedMergeTree) : Nat :=
  (forest.map fun entry => entry.tree.mergeCost).sum

/-! ## Checked event semantics -/

/-- Exact adaptive-minrun relationship recorded by a formed-run event.

The first disjunct is the `naturalLength < target` branch: `binarysort`
extends the run to `min remainingBefore target`.  The second is the already
long natural-run branch, where the final run length is unchanged. -/
def FormedLengthRelation (push : PendingPushEvent) : Prop :=
  0 < push.naturalLength ∧
    push.naturalLength ≤ push.remainingBefore ∧
    0 < push.target ∧
    ((push.naturalLength < push.target ∧
        push.run.len = min push.remainingBefore push.target) ∨
      (push.target ≤ push.naturalLength ∧
        push.run.len = push.naturalLength))

end PolicyEvent
end CPythonListsort
