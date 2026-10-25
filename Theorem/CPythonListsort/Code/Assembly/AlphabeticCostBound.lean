/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean -/

import Def.CPythonListsort.Code.Assembly.MergeCost.Part3
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Def.CPythonListsort.Code.Assembly.AlphabeticCostBound
/-!
# Entropy lower bound for alphabetic merge trees

The PowerSort upper bound is most useful when compared with the best
alphabetic merge tree on the same formed leaves.  This module proves the
standard Shannon lower bound directly for the concrete `MergeTree` cost used
by the project.  It does not assume that an optimum has already been chosen.
-/


namespace CPythonListsort

theorem exists_alphabeticMergeCost (lengths : List Nat) :
    ∃ cost, HasAlphabeticMergeCost lengths cost := by
  let plan := MergePlan.ofLengths lengths
  exact ⟨plan.mergeCost, plan, MergePlan.runLengths_ofLengths lengths, rfl⟩

end CPythonListsort
