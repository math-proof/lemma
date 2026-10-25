/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/OctanacciNumber.lean -/


import Def.Combinatorics.Enumerative.OctanacciNumber


namespace MetaMathlibExt

example : octanacciNumber 0 = 1 := by decide

example : octanacciNumber 8 = 128 := by decide

example : octanacciNumber 9 = 255 := by decide

end MetaMathlibExt
