import sympy.Basic


@[main]
private lemma main
  {x y k : ℝ}
-- given
  (h : x * k > y * k)
  (hk : k > 0) :
-- imply
  x > y := by
-- proof
  by_contra hc
  exact absurd (mul_le_mul_of_nonneg_right (le_of_not_gt hc) hk.le) (not_le.mpr h)


-- created on 2019-07-16
