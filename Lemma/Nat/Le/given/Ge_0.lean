import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  y - x ≥ 0 := by
-- proof
  exact sub_nonneg.mpr h


-- created on 2019-11-08
