import sympy.Basic


@[path]
private lemma strengthen
  {x y : ℤ}
-- given
  (h : x ≥ y + 1) :
-- imply
  x > y := by
-- proof
  omega


-- created on 2021-04-14
