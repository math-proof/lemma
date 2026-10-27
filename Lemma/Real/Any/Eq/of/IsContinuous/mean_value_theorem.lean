import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ} {a b : ℝ}
  (h₀ : ContinuousOn f (Set.uIcc a b)) :
-- imply
  ∃ c ∈ Set.uIcc a b, (∫ x in a..b, f x) = (b - a) * f c := by
-- proof
  obtain ⟨c, hc, h⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg (μ := MeasureTheory.volume)
      (g := fun _ : ℝ => (1 : ℝ)) h₀ intervalIntegrable_const fun _ _ => zero_le_one
  have h1 : (∫ x in a..b, (1 : ℝ)) = b - a := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  refine ⟨c, hc, ?_⟩
  simpa [h1, mul_comm] using h


-- created on 2020-06-15
-- updated on 2026-10-26
