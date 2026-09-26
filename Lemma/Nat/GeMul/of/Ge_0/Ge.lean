import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (hx : 0 ≤ x)
  (h : b ≤ a) :
-- imply
  b * x ≤ a * x :=
-- proof
  mul_le_mul_of_nonneg_right h hx


-- created on 2026-09-26
