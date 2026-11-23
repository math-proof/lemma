/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RiordanNumber.lean -/
module

public import Def.Combinatorics.Enumerative.RiordanNumber
public import Theorem.Finset.Enumerative.RiordanNumber
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum

public section

namespace MetaMathlibExt

example : riordanNumber 0 = 1 := by
  norm_num [riordanNumber, catalan_zero, Finset.sum_range_succ_comm]

example : riordanNumber 2 = 1 := by
  norm_num [riordanNumber, catalan_zero, catalan_one, catalan_two,
    Finset.sum_range_succ_comm]

end MetaMathlibExt
