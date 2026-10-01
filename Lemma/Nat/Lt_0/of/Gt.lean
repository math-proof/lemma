import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : y > x) :
-- imply
  x - y < 0 := by
-- proof
  exact sub_neg.mpr h


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x > y) :
-- imply
  y - x < 0 := by
-- proof
  exact sub_neg.mpr h


-- created on 2023-04-15
