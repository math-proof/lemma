import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  ∫ x in Set.Icc a b, f x = (∫ x in a..b, f x) * (if a ≤ b then 1 else 0) := by
-- proof
  split_ifs with h
  · rw [mul_one, intervalIntegral.integral_of_le h, MeasureTheory.integral_Icc_eq_integral_Ioc]
  · rw [mul_zero, Set.Icc_eq_empty h, MeasureTheory.setIntegral_empty]


-- created on 2023-06-19
