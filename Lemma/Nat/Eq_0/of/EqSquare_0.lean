import sympy.sets.sets
import sympy.Basic


@[main]
private lemma complex
  {x : ℂ}
-- given
  (h : x ^ 2 = 0) :
-- imply
  x = 0 := by
-- proof
  exact (pow_eq_zero_iff two_ne_zero).mp h


-- created on 2026-09-27
