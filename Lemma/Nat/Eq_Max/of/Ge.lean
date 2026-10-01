import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℤ}
-- given
  (h : x ≥ y) :
-- imply
  x = max x y := by
-- proof
  exact (max_eq_left h).symm


-- created on 2026-09-27
