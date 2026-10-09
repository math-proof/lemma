import Mathlib
import sympy.Basic
open Set



@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
  (hfg : ∀ x ∈ Icc a b, 0 < deriv f x) :
-- imply
  ∀ x ∈ Ico a b, f x < f b := by
-- proof
  have hmono : StrictMonoOn f (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    ·
      intro x hx
      apply (hf x hx).continuousAt.continuousWithinAt
    ·
      intro x hx
      apply hfg x (interior_subset hx)
  intro x hx
  apply hmono (Ico_subset_Icc_self hx) (right_mem_Icc.mpr (le_trans hx.1 hx.2.le)) hx.2


-- created on 2026-10-07
