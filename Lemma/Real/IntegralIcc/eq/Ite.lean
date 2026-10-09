import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ} :
-- imply
  ∫ x in Set.Icc a b, f x = if a < b then ∫ x in a..b, f x else 0 := by
-- proof
  split_ifs with h
  · rw [intervalIntegral.integral_of_le h.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  · rw [MeasureTheory.setIntegral_measure_zero _ (by rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith [not_lt.mp h])]


-- created on 2020-05-23
