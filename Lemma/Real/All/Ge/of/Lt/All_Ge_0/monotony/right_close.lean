import Mathlib
import sympy.Basic
open Set



@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (hab : a < b)
  (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
  (hfg : ∀ x ∈ Icc a b, 0 ≤ deriv f x) :
-- imply
  ∀ x ∈ Icc a b, f x ≥ f a := by
-- proof
  have hmono : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
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
  apply hmono (left_mem_Icc.mpr hab.le) hx hx.1


-- created on 2026-10-07
