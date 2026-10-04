import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  x - y ≤ 0 := by
-- proof
  exact sub_nonpos.mpr h


-- created on 2021-09-01
-- updated on 2023-03-25
