import sympy.Basic


@[main]
private lemma main
  {x y a : ℝ}
-- given
  (h : x + a ≥ y + a) :
-- imply
  x ≥ y := by
-- proof
  linarith


-- created on 2019-05-15
