import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x > y) :
-- imply
  y - x < 0 := by
-- proof
  exact sub_neg.mpr h


-- created on 2021-08-09
