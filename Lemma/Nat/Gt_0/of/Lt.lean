import sympy.Basic


@[main]
private lemma main
-- given
  (h : i < n) :
-- imply
  n > 0 := by
-- proof
  linarith


@[main]
private lemma transit
  {x y : ℝ}
-- given
  (hx : x ≥ 0)
  (h : x < y) :
-- imply
  y > 0 := by
-- proof
  exact lt_of_le_of_lt hx h


-- created on 2023-04-15
-- updated on 2026-09-27
