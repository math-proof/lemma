import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1) :
-- imply
  x ^ 2 + y ^ 2 - 1 ≤ x * y := by
-- proof
  nlinarith [mul_nonneg hx0 hy0, mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy1),
    mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr hx1)]


-- created on 2019-11-22
