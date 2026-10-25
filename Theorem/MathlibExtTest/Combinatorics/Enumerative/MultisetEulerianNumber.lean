/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MultisetEulerianNumber.lean -/


import Def.Combinatorics.Enumerative.MultisetEulerianNumber.Part2
import Def.MathlibExtTest.Combinatorics.Enumerative.MultisetEulerianNumber


namespace MetaMathlibExt

example : multisetEulerianNumber twoTwoMultiplicity 1 = 1 := by decide

example : multisetEulerianNumber twoTwoMultiplicity 2 = 4 := by decide

example : multisetEulerianNumber twoTwoMultiplicity 3 = 1 := by decide

example : multisetEulerianNumber twoTwoMultiplicity 4 = 0 := by decide

#print axioms multisetDescentNumber
#print axioms IsMultisetPermutation
#print axioms multisetEulerianNumber

end MetaMathlibExt
