import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ} :
-- imply
  |x| ≥ a ↔ x ≤ -a ∨ x ≥ a := by
-- proof
  exact le_abs'


-- created on 2022-01-07
