import sympy.Basic


@[path]
private lemma strengthen
  {x a : ℤ} :
-- imply
  x < a ↔ x ≤ a - 1 := by
-- proof
  omega


-- created on 2022-01-02
