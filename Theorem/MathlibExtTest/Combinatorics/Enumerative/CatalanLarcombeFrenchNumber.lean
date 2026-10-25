/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CatalanLarcombeFrenchNumber.lean -/


import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Def.Combinatorics.Enumerative.CatalanLarcombeFrenchNumber


namespace MetaMathlibExt

example : catalanLarcombeFrenchNumber 0 = 1 := by
  norm_num [catalanLarcombeFrenchNumber, Finset.sum_range_succ, Nat.choose]

example : catalanLarcombeFrenchNumber 1 = 8 := by
  norm_num [catalanLarcombeFrenchNumber, Finset.sum_range_succ, Nat.choose]

example : catalanLarcombeFrenchNumber 2 = 80 := by
  norm_num [catalanLarcombeFrenchNumber, Finset.sum_range_succ, Nat.choose]

end MetaMathlibExt
