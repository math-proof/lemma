/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/SquarefreeTotient.lean -/
module

public import Def.NumberTheory.PrimeCounting.SquarefreeTotient.Part2
public import Theorem.Nat.PrimeCounting.SquarefreeTotient
public import Mathlib.Tactic.NormNum

public section

namespace MathlibExtTest.NumberTheory.PrimeCounting.SquarefreeTotient

open scoped BigOperators

open MathlibExt.NumberTheory.PrimeCounting

-- Specialize the squarefree-totient lower bound at its first allowed value.
example :
    Real.log (6 + 1) + 107 / 100 <
      ∑ r ∈ Finset.Icc 1 6,
        (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
  exact moebiusSq_div_totient_sum_gt_log 6 (by norm_num)

end MathlibExtTest.NumberTheory.PrimeCounting.SquarefreeTotient
