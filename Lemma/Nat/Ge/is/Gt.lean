import sympy.Basic


@[main]
private lemma strengthen
  {x a : ℤ} :
-- imply
  x ≥ a + 1 ↔ x > a := by
-- proof
  omega


-- created on 2026-09-27
