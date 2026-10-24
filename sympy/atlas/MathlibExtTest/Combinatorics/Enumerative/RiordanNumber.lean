/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RiordanNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.RiordanNumber
import Lemma.Finset.Enumerative.RiordanNumber
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : riordanNumber 0 = 1 := by
  norm_num [riordanNumber, catalan_zero, Finset.sum_range_succ_comm]

example : riordanNumber 2 = 1 := by
  norm_num [riordanNumber, catalan_zero, catalan_one, catalan_two,
    Finset.sum_range_succ_comm]

end MetaMathlibExt
