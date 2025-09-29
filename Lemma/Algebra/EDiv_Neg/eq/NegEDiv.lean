import sympy.Basic


@[main]
private lemma main
  {a b : ℤ} :
-- imply
  a / -b = -(a / b) := by
-- proof
  apply Int.ediv_neg


-- created on 2025-03-27
