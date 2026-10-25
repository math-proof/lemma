/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Def.CPythonListsort.Code.Assembly.MergeCost.Part3
import Structure.CPythonListsort.Code.Assembly.MergeTreeCost.Part2
/-!
# Logical merge replay and final-collapse cost dominance

`MergeCost` defines the paper-facing merge tree, merge cost, weighted path
length, and their exact equality.  This module adds two pure pieces needed by
the implementation bridge:

* checked replay of the raw, pre-trim logical merge observations; and
* the exact length-and-cost semantics of CPython's `merge_force_collapse`,
  together with a proof that it costs no more than Algorithm 2's canonical
  top-pair completion.

The paper's Algorithm 2 always merges the top pair in its final loop.  CPython
has one additional branch: for a final triple `A, B, C`, it merges `A` with
`B` when `|A| < |C|`.  This is a cost-nonincreasing local tree rotation, not a
tree-equality fact.
-/

/-! ## Checked replay of logical pre-trim merges -/


namespace CPythonListsort

namespace SpannedMergeTree

/-- Apply one checked logical merge to an ordered forest.  Replay verifies the
selected index, both historical pre-trim spans, and their adjacency before
constructing an internal node. -/
def applyPoweredMergeReplayStep? (forest : List SpannedMergeTree)
    (step : PoweredMergeReplayStep) : Option (List SpannedMergeTree) := do
  let left ← forest[step.event.index]?
  let right ← forest[step.event.index + 1]?
  if left.span = step.event.left ∧ right.span = step.event.right ∧
      step.event.left.Adjacent step.event.right then
    pure (forest.take step.event.index ++
      [left.merge step.power right] ++ forest.drop (step.event.index + 2))
  else
    none

/-- Replay chronological logical merge observations. -/
def replayPoweredMergeSteps? :
    List SpannedMergeTree → List PoweredMergeReplayStep →
      Option (List SpannedMergeTree)
  | forest, [] => some forest
  | forest, step :: steps => do
      let forest ← applyPoweredMergeReplayStep? forest step
      replayPoweredMergeSteps? forest steps

/-- A powered chronological trace completely merges the supplied formed runs
into the displayed result. -/
def CompleteMergeReplay (initial : List RunSpan)
    (steps : List PoweredMergeReplayStep) (result : SpannedMergeTree) : Prop :=
  replayPoweredMergeSteps? (initial.map .leaf) steps = some [result]

/-! ## Paper top-pair completion -/

/-- Every run length in a pending forest is positive. -/
def PositiveRunLengths (lengths : List Nat) : Prop :=
  ∀ length ∈ lengths, 0 < length

/-- Cost of Algorithm 2's final loop, which repeatedly merges the top two
pending runs.  Equivalently, this is the cost of the right-associated tree on
the listed open-subtree lengths. -/
def topPairCompletionCost : List Nat → Nat
  | [] => 0
  | [_] => 0
  | first :: second :: rest =>
      first + (second :: rest).sum +
        topPairCompletionCost (second :: rest)

/-- The chronological internal-node costs paid by Algorithm 2's final loop.

The recursive definition of `topPairCompletionCost` is written from the
oldest root outward; execution merges the newest pair first, so the current
whole-forest cost is appended after the recursive suffix schedule. -/
def topPairCompletionMergeCosts : List Nat → List Nat
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      topPairCompletionMergeCosts (second :: rest) ++
        [(first :: second :: rest).sum]

end SpannedMergeTree
end CPythonListsort
