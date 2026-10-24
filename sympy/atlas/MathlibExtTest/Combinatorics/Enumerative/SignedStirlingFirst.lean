/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/SignedStirlingFirst.lean -/


import sympy.atlas.Combinatorics.Enumerative.SignedStirlingFirst
import Lemma.Finset.Enumerative.SignedStirlingFirst

namespace MetaMathlibExt

example : signedStirlingFirst 3 1 = 2 := by decide

example : signedStirlingFirst 3 2 = -3 := by decide

example : signedStirlingFirst 5 5 = 1 := signedStirlingFirst_self 5

example : signedStirlingFirst 2 3 = 0 := signedStirlingFirst_eq_zero_of_lt (by decide)

end MetaMathlibExt
