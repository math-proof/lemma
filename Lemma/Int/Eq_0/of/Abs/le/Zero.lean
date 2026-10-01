import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : |x| ≤ 0) :
-- imply
  x = 0 := by
-- proof
  exact abs_nonpos_iff.mp h


-- created on 2018-08-01
