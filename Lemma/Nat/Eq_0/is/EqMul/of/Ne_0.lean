import sympy.Basic


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {p x : α}
-- given
  (h : p ≠ 0) :
-- imply
  x = 0 ↔ x * p = 0 := by
-- proof
  constructor
  ·
    intro hx
    rw [hx, zero_mul]
  ·
    intro hxp
    exact (mul_eq_zero.mp hxp).resolve_right h


-- created on 2018-11-09
-- updated on 2026-08-20
