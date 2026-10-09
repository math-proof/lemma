import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ≥ 0) :
-- imply
  min x 0 = 0 := by
-- proof
  exact min_eq_right h


-- created on 2019-05-27
