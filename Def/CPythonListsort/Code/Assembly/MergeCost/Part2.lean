/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic
import Inductive.CPythonListsort.Code.Assembly.MergeCost
/-!
# Merge-cost accounting

This module isolates the implementation-independent arithmetic behind the
Munro--Wild PowerSort merge-cost bound.  Run lengths and merge costs remain
natural numbers; entropy and the final inequality live in `ℝ`.

An empty `MergePlan` represents the empty input.  A nonempty plan is a binary
tree whose leaves are the runs, in input order.  Internal powers are retained
for the later PowerSort-policy bridge but do not affect merge-cost accounting.
-/


namespace CPythonListsort

namespace MergeTree

/-- Leaf lengths in left-to-right input order. -/
def runLengths : MergeTree → List Nat
  | .leaf length => [length]
  | .merge _ left right => left.runLengths ++ right.runLengths

/-- Total number of elements represented by a tree. -/
def totalLength : MergeTree → Nat
  | .leaf length => length
  | .merge _ left right => left.totalLength + right.totalLength

/-- Paper merge cost: merging two subtrees costs the size of their result. -/
def mergeCost : MergeTree → Nat
  | .leaf _ => 0
  | .merge _ left right =>
      left.mergeCost + right.mergeCost + left.totalLength + right.totalLength

/-- Leaf lengths paired with their depth below an ambient root depth. -/
def leavesWithDepth : Nat → MergeTree → List (Nat × Nat)
  | depth, .leaf length => [(length, depth)]
  | depth, .merge _ left right =>
      leavesWithDepth (depth + 1) left ++ leavesWithDepth (depth + 1) right

/-- The weighted external path length at an ambient root depth. -/
def weightedPathLengthAt (depth : Nat) (tree : MergeTree) : Nat :=
  ((tree.leavesWithDepth depth).map fun leaf => leaf.1 * leaf.2).sum

/-- The ordinary weighted external path length. -/
def weightedPathLength (tree : MergeTree) : Nat :=
  tree.weightedPathLengthAt 0

end MergeTree
end CPythonListsort
