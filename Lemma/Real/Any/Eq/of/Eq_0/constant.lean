import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  -- given
  (h : ∀ x : ℝ, HasDerivAt f 0 x)
  -- imply
  : ∃ C : ℝ, ∀ x : ℝ, f x = C := by
  -- proof
  use f 0
  intro x
  by_cases hpos : 0 < x
  · have hcont : ContinuousOn f (Set.Icc 0 x) := by
      intro y _
      exact (h y).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 x) := by
      intro y _
      exact (h y).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f hpos hcont hdiff with ⟨c, _, hslope⟩
    have hder : deriv f c = 0 := (h c).deriv
    have hne : (x : ℝ) ≠ 0 := by linarith
    have hdiv : (f x - f 0) / x = 0 := by simpa [hder, sub_zero] using hslope.symm
    have : f x - f 0 = 0 := by
      have hm : x * ((f x - f 0) / x) = x * (0 : ℝ) := by rw [hdiv]
      have hleft : x * ((f x - f 0) / x) = f x - f 0 := by field_simp [hne]
      rw [hleft] at hm
      simpa using hm
    linarith
  · by_cases hneg : x < 0
    · have hcont : ContinuousOn f (Set.Icc x 0) := by
        intro y _
        exact (h y).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ f (Set.Ioo x 0) := by
        intro y _
        exact (h y).differentiableAt.differentiableWithinAt
      rcases exists_deriv_eq_slope f hneg hcont hdiff with ⟨c, _, hslope⟩
      have hder : deriv f c = 0 := (h c).deriv
      have hne : (0 : ℝ) - x ≠ 0 := by linarith
      have hdiv : (f 0 - f x) / (0 - x) = 0 := by simpa [hder] using hslope.symm
      have : f 0 - f x = 0 := by
        have hm : (0 - x) * ((f 0 - f x) / (0 - x)) = (0 - x) * (0 : ℝ) := by rw [hdiv]
        have hleft : (0 - x) * ((f 0 - f x) / (0 - x)) = f 0 - f x := by field_simp [hne]
        rw [hleft] at hm
        simpa using hm
      linarith
    · have hz : x = 0 := by linarith
      rw [hz]

-- created on 2020-06-12
