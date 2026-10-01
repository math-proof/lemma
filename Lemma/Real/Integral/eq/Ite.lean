import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  ∫ x in a..b, f x = if a > b then -∫ x in Set.Icc b a, f x else ∫ x in Set.Icc a b, f x := by
-- proof
  split_ifs with h
  · rw [intervalIntegral.integral_of_ge h.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  · rw [intervalIntegral.integral_of_le (not_lt.mp h), MeasureTheory.integral_Icc_eq_integral_Ioc]


-- created on 2020-05-24
