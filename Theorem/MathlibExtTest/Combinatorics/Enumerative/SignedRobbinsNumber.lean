/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/SignedRobbinsNumber.lean -/


import Def.Combinatorics.Enumerative.SignedRobbinsNumber


namespace MetaMathlibExt

example : robbinsNumber 0 = 1 := by decide

example : robbinsNumber 3 = 7 := by decide

example : signedRobbinsNumber 0 = 1 := by decide

example : signedRobbinsNumber 2 = -7 := by decide

end MetaMathlibExt
