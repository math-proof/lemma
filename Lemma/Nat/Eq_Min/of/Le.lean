import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  x = min x y := by
-- proof
  exact (min_eq_left h).symm


-- created on 2026-09-27
