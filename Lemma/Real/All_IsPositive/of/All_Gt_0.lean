import Mathlib
import sympy.Basic
open Set



@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : ∀ x ∈ Ioo a b, deriv f x > 0) :
-- imply
  ∀ x ∈ Ioo a b, deriv f x ∈ Ioi 0 := by
-- proof
  intro x hx
  apply h x hx


-- created on 2026-10-07
