import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b d : ℝ}
-- given
  (_h : ∀ x, f x ≥ 0) :
-- imply
  ∫ x in Set.Icc a b, f x = ∫ x in Set.Icc (a - d) (b - d), f (x + d) := by
-- proof
  rcases le_or_gt a b with hab | hab
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_add_right, sub_add_cancel, sub_add_cancel]
  · rw [Set.Icc_eq_empty (not_le.mpr hab), Set.Icc_eq_empty (not_le.mpr (by linarith)), MeasureTheory.setIntegral_empty,
      MeasureTheory.setIntegral_empty]


-- created on 2020-05-22
