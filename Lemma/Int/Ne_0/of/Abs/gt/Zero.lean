import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x : ℝ}
-- given
  (h : |x| > 0) :
-- imply
  x ≠ 0 := by
-- proof
  exact abs_pos.mp h


-- created on 2020-02-13
