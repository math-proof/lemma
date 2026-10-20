import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import sympy.Basic
open MeasureTheory Real Set


/--
For the joint density `exp(-x)` on `0 < y < x`, the conditional probability `P(x > 5 | y ≤ 3)`
equals `3 / (exp 5 - exp 2)`. The numerator is `∫_{5}^{∞} 3 exp(-x)` and the denominator is
`1 - exp(-3)`.
-/
@[path]
private lemma main :
-- imply
  (∫ x in Ioi (5 : ℝ), 3 * exp (-x)) /
      ((∫ x in Ioi (0 : ℝ), exp (-x)) - ∫ x in Ioi (3 : ℝ), exp (-x)) =
    3 / (exp 5 - exp 2) := by
-- proof
  rw [integral_const_mul, integral_exp_neg_Ioi, integral_exp_neg_Ioi_zero, integral_exp_neg_Ioi]
  have hne : (1 - exp (-3) : ℝ) ≠ 0 := by
    have : exp (-3) < 1 := by simp [exp_lt_one_iff]
    linarith
  have hpos : exp 5 - exp 2 ≠ 0 := by
    have : exp 2 < exp 5 := exp_lt_exp.mpr (by norm_num)
    linarith
  have h : exp (-5) * (exp 5 - exp 2) = 1 - exp (-3) := by
    rw [mul_sub, ← exp_add, ← exp_add]
    norm_num
  rw [eq_div_iff hpos, div_mul_eq_mul_div, mul_assoc, h]
  field_simp [hne]


-- created on 2023-03-20
-- updated on 2026-10-17
