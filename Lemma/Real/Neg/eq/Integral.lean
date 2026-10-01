import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  -∫ x in a..b, f x = ∫ x in b..a, f x := by
-- proof
  exact (intervalIntegral.integral_symm a b).symm


-- created on 2020-05-24
