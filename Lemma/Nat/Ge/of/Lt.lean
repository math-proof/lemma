import sympy.sets.sets
import sympy.Basic


@[main]
private lemma relax
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  y ≥ x := by
-- proof
  exact h.le


-- created on 2026-09-27
