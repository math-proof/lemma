import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h : x ∈ ({a, b} : Set ℝ)) :
-- imply
  x = a ∨ x = b := by
-- proof
  simpa using h


-- created on 2026-09-27
