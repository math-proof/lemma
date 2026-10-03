import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b y : ℝ} :
-- imply
  (∫ x : ℝ in a..b, f x) * y = ∫ x : ℝ in a..b, f x * y :=
-- proof
  (intervalIntegral.integral_mul_const y f).symm


-- created on 2026-10-03
