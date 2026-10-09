import sympy.Basic


@[path]
private lemma main
  {x y k : ℤ}
-- given
  (h : x * k > y * k)
  (hk : k < 0) :
-- imply
  x < y := by
-- proof
  by_contra hc
  exact absurd (mul_le_mul_of_nonpos_right (not_lt.mp hc) hk.le) (not_le.mpr h)


-- created on 2019-12-16
