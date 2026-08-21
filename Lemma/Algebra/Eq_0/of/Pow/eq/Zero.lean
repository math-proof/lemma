import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
  {n : ℕ}
-- given
  (h : x ^ n = 0)
  (hn : n > 0) :
-- imply
  x = 0 := by
-- proof
  exact (pow_eq_zero_iff hn.ne').mp h


-- created on 2018-11-03
-- updated on 2026-08-20
