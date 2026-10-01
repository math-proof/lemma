import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma mean_value_theorem.Lagrange
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : a < b)
  (hc : ContinuousOn f (Set.Icc a b))
  (hd : DifferentiableOn ℝ f (Set.Ioo a b)) :
-- imply
  ∃ z ∈ Set.Ioo a b, f b - f a = (b - a) * deriv f z := by
-- proof
  obtain ⟨z, hz, hdz⟩ := exists_deriv_eq_slope f h hc hd
  have hne : b - a ≠ 0 := sub_ne_zero.mpr h.ne'
  refine ⟨z, hz, ?_⟩
  rw [hdz]
  field_simp


-- created on 2026-09-27
