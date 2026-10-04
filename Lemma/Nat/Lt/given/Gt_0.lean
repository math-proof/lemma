import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : y - x > 0) :
-- imply
  x < y := by
-- proof
  linarith


-- created on 2019-06-24
