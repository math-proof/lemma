import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b) :
-- imply
  |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
-- proof
  exact intervalIntegral.abs_integral_le_integral_abs hab


-- created on 2023-04-15
