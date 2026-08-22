import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
  {n : ℕ}
-- given
  (h_n : n > 0)
  (h_a : 0 ≤ a)
  (h : x > a) :
-- imply
  x ^ n > a ^ n :=
-- proof
  pow_lt_pow_left₀ h h_a h_n.ne'


-- created on 2023-04-15
-- updated on 2026-08-22
