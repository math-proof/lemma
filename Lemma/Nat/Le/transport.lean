import sympy.Basic


@[main]
private lemma main
  {x y a : ℝ}
-- given
  (h : x ≤ y - a) :
-- imply
  x + a ≤ y := by
-- proof
  exact le_sub_iff_add_le.mp h


-- created on 2019-09-05
