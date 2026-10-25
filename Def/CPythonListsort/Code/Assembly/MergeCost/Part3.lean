/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic
import Inductive.CPythonListsort.Code.Assembly.MergeCost.Part2
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

namespace MergePlan

def runLengths : MergePlan → List Nat
  | .empty => []
  | .tree root => root.runLengths

def mergeCost : MergePlan → Nat
  | .empty => 0
  | .tree root => root.mergeCost

def leavesWithDepth : MergePlan → List (Nat × Nat)
  | .empty => []
  | .tree root => root.leavesWithDepth 0

def weightedPathLength : MergePlan → Nat
  | .empty => 0
  | .tree root => root.weightedPathLength

end MergePlan
end MergeTree
end CPythonListsort
