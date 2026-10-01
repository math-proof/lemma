import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x - y > 0) :
-- imply
  x > y := by
-- proof
  exact sub_pos.mp h


-- created on 2019-06-12
