import sympy.Basic


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  a > 0 := by
-- proof
  linarith [h]


-- created on 2025-05-04
