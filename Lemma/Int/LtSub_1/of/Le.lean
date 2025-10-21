import sympy.Basic


@[main, comm 1]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  linarith


-- created on 2025-03-28
-- updated on 2025-05-03
