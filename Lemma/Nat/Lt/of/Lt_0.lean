import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x - y < 0) :
-- imply
  x < y := by
-- proof
  exact sub_neg.mp h


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x - y < 0) :
-- imply
  x < y := by
-- proof
  exact sub_neg.mp h


-- created on 2021-08-27
