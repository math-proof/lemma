import sympy.sets.sets
import sympy.Basic


@[main]
private lemma relax
  {x y : ℤ} :
-- imply
  x ≤ y ↔ x < y + 1 := by
-- proof
  omega


@[main]
private lemma strengthen
  {x a : ℤ} :
-- imply
  x + 1 ≤ a ↔ x < a := by
-- proof
  omega


-- created on 2023-11-05
