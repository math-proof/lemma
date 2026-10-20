import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.SquarefreeTotient
open scoped BigOperators
open MathlibExt.NumberTheory.PrimeCounting


/--
[moebiusSq_div_totient_sum_gt_log](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotient.lean)
-/
@[path]
private lemma moebiusSq_div_totient_sum_gt_log_eq
  {z : ℕ}
-- given
  (hz : 6 ≤ z) :
-- imply
  Real.log (z + 1) + 107 / 100 <
    ∑ r ∈ Finset.Icc 1 z,
    (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.moebiusSq_div_totient_sum_gt_log z hz


-- created on 2026-10-20
