/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeCost
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropy lower bound for alphabetic merge trees

The PowerSort upper bound is most useful when compared with the best
alphabetic merge tree on the same formed leaves.  This module proves the
standard Shannon lower bound directly for the concrete `MergeTree` cost used
by the project.  It does not assume that an optimum has already been chosen.
-/

namespace CPythonListsort

/-- Entropy multiplied by its total mass, written without normalized list
fractions.  Positivity hypotheses in the lemmas below keep every logarithm on
its intended positive domain. -/
noncomputable def weightedBinaryEntropy (total : Nat)
    (lengths : List Nat) : Real :=
  (lengths.map fun length : Nat =>
    (length : Real) * Real.logb 2 ((total : Real) / (length : Real))).sum

/-- A concrete right-associated alphabetic tree on one nonempty length list.
Its labels are irrelevant to cost and are set to zero. -/
def ofLengths : Nat → List Nat → MergeTree
  | first, [] => .leaf first
  | first, second :: rest =>
      .merge 0 (.leaf first) (ofLengths second rest)

/-- A concrete alphabetic plan for every length list, including the empty
list.  It witnesses that the set minimized below is never empty. -/
def ofLengths : List Nat → MergePlan
  | [] => .empty
  | first :: rest => .tree (MergeTree.ofLengths first rest)

/-- A natural number occurs as the merge cost of an alphabetic plan with the
given left-to-right leaf lengths. -/
def HasAlphabeticMergeCost (lengths : List Nat) (cost : Nat) : Prop :=
  ∃ plan : MergePlan,
    plan.runLengths = lengths ∧ plan.mergeCost = cost

theorem exists_alphabeticMergeCost (lengths : List Nat) :
    ∃ cost, HasAlphabeticMergeCost lengths cost := by
  let plan := MergePlan.ofLengths lengths
  exact ⟨plan.mergeCost, plan, MergePlan.runLengths_ofLengths lengths, rfl⟩

/-- Minimum merge cost among all alphabetic plans with the displayed leaf
sequence.  `Nat.find` is legitimate because `MergePlan.ofLengths` gives an
explicit witness for every list, including `[]`. -/
noncomputable def optimalAlphabeticMergeCost (lengths : List Nat) : Nat :=
  by
    classical
    exact Nat.find (exists_alphabeticMergeCost lengths)
