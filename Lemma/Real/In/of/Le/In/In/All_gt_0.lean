import Mathlib
import sympy.Basic
open Set



@[path]
private lemma main
  {a b x0 x1 : ℝ}
  {f : ℝ → ℝ}
  {n : ℕ}
-- given
  (hle : x0 ≤ x1)
  (hx0 : x0 ∈ Ioo a b)
  (hx1 : x1 ∈ Ioo a b)
  (hf : ∀ x ∈ Ioo a b, 0 < iteratedDeriv (n + 1) f x) :
-- imply
  iteratedDeriv n f x0 ≤ iteratedDeriv n f x1 := by
-- proof
  have hderiv : ∀ x ∈ Ioo a b, 0 < deriv (iteratedDeriv n f) x := by
    intro x hx
    have h := hf x hx
    rwa [iteratedDeriv_succ] at h
  have hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ (iteratedDeriv n f) x := by
    intro x hx
    by_contra h
    have hpos := hderiv x hx
    rw [deriv_zero_of_not_differentiableAt h] at hpos
    apply lt_irrefl 0 hpos
  have hmono : StrictMonoOn (iteratedDeriv n f) (Ioo a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo a b)
    ·
      intro x hx
      apply (hdiff x hx).differentiableWithinAt.continuousWithinAt
    ·
      intro x hx
      apply hderiv x
      rwa [interior_Ioo] at hx
  if h : x0 = x1 then
    subst h
    apply le_refl
  else
    apply le_of_lt
    apply hmono hx0 hx1 (lt_of_le_of_ne hle h)


-- created on 2026-10-07
