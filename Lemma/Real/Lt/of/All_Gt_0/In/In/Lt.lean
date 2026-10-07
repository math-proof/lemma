import Mathlib
import sympy.Basic
open Set



@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b x₀ x₁ : ℝ}
-- given
  (hf : ∀ x ∈ Ioo a b, deriv f x > 0)
  (h0 : x₀ ∈ Ioo a b)
  (h1 : x₁ ∈ Ioo a b)
  (hlt : x₀ < x₁) :
-- imply
  f x₀ < f x₁ := by
-- proof
  apply strictMonoOn_of_deriv_pos (convex_Ioo a b) _ _ h0 h1 hlt
  · apply fun x hx ↦ ((differentiableAt_of_deriv_ne_zero (ne_of_gt (hf x hx))).differentiableWithinAt).continuousWithinAt
  · apply fun x hx ↦ hf x (interior_subset hx)


-- created on 2026-10-07
