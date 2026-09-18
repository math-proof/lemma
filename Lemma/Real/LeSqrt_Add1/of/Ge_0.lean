import sympy.core.power
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  √x ≤ 1 + x := by
-- proof
  have h : 0 ≤ (√x - 1) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hx] at h
  linarith [h]


-- created on 2026-09-18
