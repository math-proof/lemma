import Mathlib.Algebra.Order.Field.Basic
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (hx : x < 0)
  (h : a ≥ b) :
-- imply
  a / x ≤ b / x := by
-- proof
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonpos_right h (inv_nonpos.mpr hx.le)


-- created on 2021-04-25
-- updated on 2026-10-17
