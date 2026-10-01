import sympy.Basic


@[main]
private lemma strengthen
  {x a : ℤ} :
-- imply
  x < a ↔ a ≥ x + 1 := by
-- proof
  omega


-- created on 2026-09-27
