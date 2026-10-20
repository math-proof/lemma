import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : ContinuousOn f (Set.Ico a b))
  (h₁ : ∀ x ∈ Set.Ico a b, deriv f x > 0) :
-- imply
  ∀ x ∈ Set.Ioo a b, f x > f a := by
-- proof
  intro x hx
  apply strictMonoOn_of_deriv_pos (convex_Ico a b) h₀ _ ⟨le_rfl, lt_trans hx.1 hx.2⟩ (Set.Ioo_subset_Ico_self hx) hx.1
  intro y hy
  rw [interior_Ico] at hy
  apply h₁ y (Set.Ioo_subset_Ico_self hy)


-- created on 2020-06-03
-- updated on 2026-10-17
