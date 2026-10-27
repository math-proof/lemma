import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : ContinuousOn f (Set.Ico a b))
  (h₁ : DifferentiableOn ℝ f (Set.Ioo a b))
  (h₂ : ∀ x ∈ Set.Ico a b, deriv f x ≥ 0) :
-- imply
  ∀ x ∈ Set.Ico a b, f x ≥ f a := by
-- proof
  intro x hx
  apply monotoneOn_of_deriv_nonneg (convex_Ico a b) h₀ _ _ ⟨le_rfl, lt_of_le_of_lt hx.1 hx.2⟩ hx hx.1
  ·
    rwa [interior_Ico]
  ·
    intro y hy
    rw [interior_Ico] at hy
    apply h₂ y (Set.Ioo_subset_Ico_self hy)


-- created on 2023-10-03
-- updated on 2026-10-26
