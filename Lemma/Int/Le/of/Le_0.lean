import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x - y ≤ 0) :
-- imply
  x ≤ y := by
-- proof
  linarith


-- created on 2021-09-01
