import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  x - y ≤ 0 := by
-- proof
  linarith


@[main]
private lemma given
  {a b : ℝ}
-- given
  (h : a ≤ b) :
-- imply
  a - b ≤ 0 := by
-- proof
  linarith


-- created on 2026-09-27
