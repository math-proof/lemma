import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≠ y) :
-- imply
  (if x = y then (1 : ℝ) else 0) = 0 := by
-- proof
  exact if_neg h


-- created on 2026-09-27
