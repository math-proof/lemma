import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℤ} :
-- imply
  x ≥ y ↔ x > y - 1 := by
-- proof
  constructor <;> intro h <;> omega


-- created on 2023-11-05
