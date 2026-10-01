import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  x ≤ 0 := by
-- proof
  exact h.le


-- created on 2026-09-27
