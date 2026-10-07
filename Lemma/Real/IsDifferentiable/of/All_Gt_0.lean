import Mathlib
import sympy.Basic
open Set



@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (h : ∀ x ∈ Ioo a b, 0 < iteratedDeriv 2 f x) :
-- imply
  ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := by
-- proof
  sorry


-- created on 2026-10-07
