import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x > y) :
-- imply
  x - y > 0 := by
-- proof
  exact sub_pos.mpr h


-- created on 2019-06-12
