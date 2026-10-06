import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
  -- given
  (hle : a ≤ b)
  (hcont : ContinuousOn f (Set.Icc a b))
  (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
  -- imply
  : ∃ z ∈ Set.Icc a b, f b - f a = (b - a) * deriv f z := by
  -- proof
  by_cases hlt : a < b
  · rcases exists_deriv_eq_slope f hlt hcont hdiff with ⟨z, hz, hslope⟩
    refine ⟨z, ⟨hz.1.le, hz.2.le⟩, ?_⟩
    have hne : b - a ≠ 0 := by linarith
    have : f b - f a = (b - a) * deriv f z := by
      rw [hslope]
      field_simp [hne]
      <;> ring
    exact this
  · have heq : a = b := by linarith
    subst heq
    refine ⟨a, ?_, ?_⟩
    · simp
    · simp

-- created on 2020-06-17
