import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
  {n : ℕ}
-- given
  (hx : x = 0)
  (hn : n > 0) :
-- imply
  x ^ n = 0 := by
-- proof
  rw [hx]
  exact zero_pow hn.ne'


-- created on 2018-11-03
-- updated on 2026-08-20
