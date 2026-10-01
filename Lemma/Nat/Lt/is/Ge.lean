import sympy.Basic


@[main]
private lemma strengthen
  {x a : ℤ} :
-- imply
  x < a ↔ a ≥ x + 1 := by
-- proof
  omega


-- created on 2021-12-17
