/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MultisetEulerianNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.MultisetEulerianNumber

namespace MetaMathlibExt

private def twoTwoMultiplicity : Fin 2 → ℕ := fun _ => 2

example : multisetEulerianNumber twoTwoMultiplicity 1 = 1 := by decide
example : multisetEulerianNumber twoTwoMultiplicity 2 = 4 := by decide
example : multisetEulerianNumber twoTwoMultiplicity 3 = 1 := by decide
example : multisetEulerianNumber twoTwoMultiplicity 4 = 0 := by decide

#print axioms multisetDescentNumber
#print axioms IsMultisetPermutation
#print axioms multisetEulerianNumber

end MetaMathlibExt
