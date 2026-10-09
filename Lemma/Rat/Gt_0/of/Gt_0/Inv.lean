import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x : ℝ}
-- given
  (h : 1 / x > 0) :
-- imply
  x > 0 := by
-- proof
  exact one_div_pos.mp h


-- created on 2019-08-09
