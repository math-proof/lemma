import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  |x| > 0 := by
-- proof
  exact abs_pos.mpr h.ne


-- created on 2020-01-17
