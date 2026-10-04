import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n % 2 ≠ 0) :
-- imply
  n % 2 = 1 := by
-- proof
  omega


-- created on 2020-01-27
-- updated on 2023-05-22
