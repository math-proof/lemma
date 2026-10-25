/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic
import Def.CPythonListsort.Code.Assembly.MergeCost.Part2
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

@[simp]
theorem sum_runLengths : ∀ tree : MergeTree,
    tree.runLengths.sum = tree.totalLength
  | .leaf _ => by simp [runLengths, totalLength]
  | .merge _ left right => by
      simp [runLengths, totalLength, sum_runLengths left, sum_runLengths right]

@[simp]
theorem leavesWithDepth_fst (depth : Nat) : ∀ tree : MergeTree,
    (tree.leavesWithDepth depth).map Prod.fst = tree.runLengths
  | .leaf _ => by simp [leavesWithDepth, runLengths]
  | .merge _ left right => by
      simp [leavesWithDepth, runLengths, leavesWithDepth_fst (depth + 1) left,
        leavesWithDepth_fst (depth + 1) right]

/-- Weighted path length at depth `d` is intrinsic merge cost plus `d` copies
of every leaf weight. -/
theorem weightedPathLengthAt_eq (depth : Nat) : ∀ tree : MergeTree,
    tree.weightedPathLengthAt depth =
      tree.mergeCost + depth * tree.totalLength
  | .leaf length => by
      simp [weightedPathLengthAt, leavesWithDepth, mergeCost, totalLength,
        Nat.mul_comm]
  | .merge power left right => by
      rw [weightedPathLengthAt, leavesWithDepth, List.map_append, List.sum_append,
        mergeCost, totalLength]
      change
        left.weightedPathLengthAt (depth + 1) +
            right.weightedPathLengthAt (depth + 1) =
          left.mergeCost + right.mergeCost + left.totalLength +
              right.totalLength +
            depth * (left.totalLength + right.totalLength)
      rw [weightedPathLengthAt_eq (depth + 1) left,
        weightedPathLengthAt_eq (depth + 1) right]
      ring

end MergeTree
end CPythonListsort
