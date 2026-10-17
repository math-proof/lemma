import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : ContinuousOn f (Set.Icc a b))
  (h₁ : DifferentiableOn ℝ f (Set.Ioo a b))
  (h₂ : ∀ x ∈ Set.Icc a b, deriv f x ≥ 0) :
-- imply
  ∀ x ∈ Set.Icc a b, f x ≥ f a := by
-- proof
  intro x hx
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) h₀ _ _ ⟨le_rfl, le_trans hx.1 hx.2⟩ hx hx.1
  ·
    rwa [interior_Icc]
  ·
    intro y hy
    rw [interior_Icc] at hy
    apply h₂ y (Set.Ioo_subset_Icc_self hy)


-- created on 2026-10-11
-- updated on 2026-10-17
