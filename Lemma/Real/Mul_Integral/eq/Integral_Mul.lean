import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b y : ℝ} :
-- imply
  (∫ x : ℝ in a..b, f x) * y = ∫ x : ℝ in a..b, f x * y :=
-- proof
  (intervalIntegral.integral_mul_const y f).symm


-- created on 2020-06-06
