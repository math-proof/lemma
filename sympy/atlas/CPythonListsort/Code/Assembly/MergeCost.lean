/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

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

/-- A positive run-length sequence with prescribed total length. -/
structure RunProfile (n : Nat) where
  lengths : List Nat
  sum_eq : lengths.sum = n
  positive : ∀ length ∈ lengths, 0 < length

namespace RunProfile

/-- Real-valued run fractions, with Lean's totalized division convention at
total length zero. -/
noncomputable def fractions (profile : RunProfile n) : List ℝ :=
  profile.lengths.map fun length : Nat => (length : ℝ) / (n : ℝ)

end RunProfile

/-- One base-two Shannon entropy summand, using `0⁻¹ = 0` and
`Real.logb 2 0 = 0` at the zero endpoint. -/
noncomputable def binaryEntropyTerm (p : ℝ) : ℝ :=
  p * Real.logb 2 p⁻¹

/-- Base-two Shannon entropy of a finite real-valued weight list. -/
noncomputable def binaryEntropy (weights : List ℝ) : ℝ :=
  (weights.map binaryEntropyTerm).sum

/-- Base-two entropy of the fractions represented by a run profile. -/
noncomputable def RunProfile.entropy (profile : RunProfile n) : ℝ :=
  binaryEntropy profile.fractions

/-- A binary merge tree.  Leaves store run lengths and each internal node
retains its PowerSort node power for the later policy bridge. -/
inductive MergeTree where
  | leaf (length : Nat)
  | merge (power : Nat) (left right : MergeTree)
  deriving DecidableEq, Repr

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

/-- A full merge plan, including the empty-input case. -/
inductive MergePlan where
  | empty
  | tree (root : MergeTree)
  deriving DecidableEq, Repr

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
