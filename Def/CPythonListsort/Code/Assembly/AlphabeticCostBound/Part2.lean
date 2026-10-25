/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AlphabeticCostBound.lean -/

import Def.CPythonListsort.Code.Assembly.MergeCost.Part3
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Theorem.CPythonListsort.Code.Assembly.AlphabeticCostBound
/-!
# Entropy lower bound for alphabetic merge trees

The PowerSort upper bound is most useful when compared with the best
alphabetic merge tree on the same formed leaves.  This module proves the
standard Shannon lower bound directly for the concrete `MergeTree` cost used
by the project.  It does not assume that an optimum has already been chosen.
-/


namespace CPythonListsort

/-- Minimum merge cost among all alphabetic plans with the displayed leaf
sequence.  `Nat.find` is legitimate because `MergePlan.ofLengths` gives an
explicit witness for every list, including `[]`. -/
noncomputable def optimalAlphabeticMergeCost (lengths : List Nat) : Nat :=
  by
    classical
    exact Nat.find (exists_alphabeticMergeCost lengths)

end CPythonListsort
