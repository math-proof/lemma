/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Words/FirstDifference.lean -/


import sympy.atlas.Combinatorics.Words.FirstDifference
import Lemma.Finset.Words.FirstDifference

namespace MetaMathlibExt

example (w : ℕ → ZMod 2) : firstDifference w 0 = w 1 - w 0 := by
  rfl

example : firstDifferenceList [] = [] := by
  rfl

example : firstDifferenceList ([0, 1, 1, 0, 1, 0] : List (ZMod 2)) = [1, 0, 1, 1, 1] := by
  decide

#print axioms firstDifference
#print axioms firstDifferenceList
#print axioms length_firstDifferenceList

end MetaMathlibExt
