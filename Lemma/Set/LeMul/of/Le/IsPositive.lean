import Mathlib.Algebra.Order.Field.Basic
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : a ≤ b)
  (hx : 0 < x) :
-- imply
  a * x ≤ b * x :=
-- proof
  mul_le_mul_of_nonneg_right h hx.le


-- created on 2021-04-25
-- updated on 2026-10-17
