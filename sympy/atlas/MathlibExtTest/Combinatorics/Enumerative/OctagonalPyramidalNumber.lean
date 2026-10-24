/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/OctagonalPyramidalNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.OctagonalPyramidalNumber

namespace MetaMathlibExt

example : octagonalPyramidalNumber 1 = 1 := by decide
example : octagonalPyramidalNumber 4 = 70 := by decide

/-- Regression for the restricted-composition side of the correspondence. -/
example : (octagonalPyramidalCompositions 2).card = 9 := by decide

end MetaMathlibExt
