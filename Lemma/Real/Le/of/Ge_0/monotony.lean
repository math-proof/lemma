import Mathlib
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b x : ℝ}
-- given
  (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
  (hf : ∀ t ∈ Set.Icc a b, 0 ≤ deriv f t)
  (hx : x ∈ Set.Icc a b) :
-- imply
  f x ≤ f b := by
-- proof
  obtain ⟨hxa, hxb⟩ := Set.mem_Icc.mp hx
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) _ _ _ hx (Set.right_mem_Icc.mpr (hxa.trans hxb)) hxb
  · apply fun t ht ↦ (hd t ht).differentiableWithinAt.continuousWithinAt
  · apply fun t ht ↦ (hd t (interior_subset ht)).differentiableWithinAt
  · apply fun t ht ↦ hf t (interior_subset ht)


-- created on 2026-10-07
