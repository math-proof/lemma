import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  x - y < 0 := by
-- proof
  exact sub_neg.mpr h


-- created on 2021-08-27
-- updated on 2023-03-25
