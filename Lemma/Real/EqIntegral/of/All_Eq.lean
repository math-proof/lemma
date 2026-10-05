import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (h : Set.EqOn f g (Set.Ioo a b)) :
-- imply
  ∫ x in a..b, f x = ∫ x in a..b, g x := by
-- proof
  exact intervalIntegral.integral_congr_Ioo_of_le hab h


-- created on 2020-03-29
