import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  ∫ x in a..b, f x = -∫ x in b..a, f x := by
-- proof
  rw [intervalIntegral.integral_symm a b, neg_neg]


-- created on 2020-05-23
