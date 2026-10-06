import sympy.Basic


@[main]
private lemma main
  {x y t : ℝ}
-- given
  (h : y ≤ x) :
-- imply
  y + t ≤ x + t := by
-- proof
  linarith


-- created on 2020-06-26
