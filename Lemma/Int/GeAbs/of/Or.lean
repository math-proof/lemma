import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a : ℝ}
-- given
  (h : x ≤ -a ∨ x ≥ a) :
-- imply
  |x| ≥ a := by
-- proof
  exact le_abs'.mpr h


-- created on 2026-09-27
