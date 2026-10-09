import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : |x| ≠ 0) :
-- imply
  x ≠ 0 := by
-- proof
  exact abs_ne_zero.mp h


-- created on 2026-10-03
