import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {n : ℤ}
-- given
  (h : x > 0) :
-- imply
  x ^ n > 0 :=
-- proof
  zpow_pos h n


-- created on 2018-08-22
-- updated on 2026-08-20
