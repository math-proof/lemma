/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/FubiniNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.FubiniNumber

namespace MetaMathlibExt

example : (List.range 5).map fubiniNumber = [1, 1, 3, 13, 75] := by decide

example : fubiniNumber 0 = 1 := by simp

example : fubiniNumber 1 = 1 := by simp

example : fubiniNumber 2 = 3 := fubiniNumber_two

end MetaMathlibExt
