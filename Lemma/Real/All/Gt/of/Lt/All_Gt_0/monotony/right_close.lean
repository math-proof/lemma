import Mathlib
import sympy.Basic
open Set



@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (hab : a < b)
  (hf : ∀ x ∈ Icc a b, 0 < deriv f x) :
-- imply
  ∀ x ∈ Ioc a b, f a < f x := by
-- proof
  have hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x := by
    intro x hx
    by_contra h
    have hpos := hf x hx
    rw [deriv_zero_of_not_differentiableAt h] at hpos
    apply lt_irrefl 0 hpos
  have hmono : StrictMonoOn f (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    ·
      intro x hx
      apply (hdiff x hx).differentiableWithinAt.continuousWithinAt
    ·
      intro x hx
      apply hf x
      apply Ioo_subset_Icc_self
      rwa [interior_Icc] at hx
  intro x hx
  apply hmono _ (Ioc_subset_Icc_self hx) hx.1
  apply left_mem_Icc.mpr hab.le


-- created on 2026-10-07
