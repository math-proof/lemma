import sympy.sets.sets
import sympy.Basic


@[main]
private lemma strengthen.minus
  {x y : ℤ}
-- given
  (h : x > y) :
-- imply
  x - 1 ≥ y := by
-- proof
  omega


-- created on 2026-09-27
