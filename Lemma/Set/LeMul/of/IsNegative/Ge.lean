import Mathlib.Algebra.Order.Field.Basic
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (hx : x < 0)
  (h : a ≥ b) :
-- imply
  a * x ≤ b * x :=
-- proof
  mul_le_mul_of_nonpos_right h hx.le


-- created on 2023-10-15
-- updated on 2026-10-17
