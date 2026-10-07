import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x > y) :
-- imply
  x ≥ y + 1 := by
-- proof
  omega


-- created on 2021-04-14
-- updated on 2023-11-05
