import Mathlib
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b x : ℝ}
-- given
  (hf : ∀ t ∈ Set.Icc a b, deriv f t > 0)
  (hx : x ∈ Set.Icc a b) :
-- imply
  f a ≤ f x := by
-- proof
  obtain ⟨hxa, hxb⟩ := Set.mem_Icc.mp hx
  obtain hlt | rfl := lt_or_eq_of_le hxa
  ·
    apply le_of_lt
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) _ _ (Set.left_mem_Icc.mpr (hxa.trans hxb)) hx hlt
    · apply fun t ht ↦ ((differentiableAt_of_deriv_ne_zero (ne_of_gt (hf t ht))).differentiableWithinAt).continuousWithinAt
    · apply fun t ht ↦ hf t (interior_subset ht)
  · apply le_refl _


-- created on 2026-10-07
