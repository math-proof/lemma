import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : ContinuousOn f (Set.Icc a b))
  (h₁ : ∀ x ∈ Set.Icc a b, deriv f x > 0) :
-- imply
  ∀ x ∈ Set.Ioc a b, f x > f a := by
-- proof
  intro x hx
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) h₀ _ ⟨le_rfl, le_trans hx.1.le hx.2⟩ (Set.Ioc_subset_Icc_self hx) hx.1
  intro y hy
  rw [interior_Icc] at hy
  apply h₁ y (Set.Ioo_subset_Icc_self hy)


-- created on 2020-06-02
-- updated on 2026-10-17
