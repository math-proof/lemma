import Mathlib
import sympy.Basic
open Set



@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
  (hfg : ∀ x ∈ Icc a b, deriv f x ≤ 0) :
-- imply
  ∀ x ∈ Icc a b, f x ≤ f a := by
-- proof
  have hmono : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    ·
      intro x hx
      apply (hf x hx).continuousAt.continuousWithinAt
    ·
      intro x hx
      apply (hf x (interior_subset hx)).differentiableWithinAt
    ·
      intro x hx
      apply hfg x (interior_subset hx)
  intro x hx
  apply hmono (left_mem_Icc.mpr (le_trans hx.1 hx.2)) hx hx.1


-- created on 2026-10-07
