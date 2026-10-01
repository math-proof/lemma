import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ} :
-- imply
  x ≤ -a ∨ x ≥ a ↔ |x| ≥ a := by
-- proof
  exact le_abs'.symm


-- created on 2023-04-18
