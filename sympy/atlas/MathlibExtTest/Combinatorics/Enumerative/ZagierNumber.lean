/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ZagierNumber.lean -/


import Mathlib.Tactic.NormNum
import sympy.atlas.Combinatorics.Enumerative.ZagierNumber

namespace MetaMathlibExt

example : zagierNumber 0 = 1 := by
  norm_num [zagierNumber, dombTypeSum, Finset.sum_range_succ, Nat.choose]

example : zagierNumber 1 = 4 := by
  norm_num [zagierNumber, dombTypeSum, Finset.sum_range_succ, Nat.choose]

example : zagierNumber 2 = 20 := by
  norm_num [zagierNumber, dombTypeSum, Finset.sum_range_succ, Nat.choose]

example : zagierNumber 3 = 112 := by
  norm_num [zagierNumber, dombTypeSum, Finset.sum_range_succ, Nat.choose]

end MetaMathlibExt
