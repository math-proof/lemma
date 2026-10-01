import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| ≥ a) :
-- imply
  x ≤ -a ∨ x ≥ a := by
-- proof
  exact le_abs'.mp h


-- created on 2018-07-29
