import sympy.Basic


@[path]
private lemma main
  {x y r : ℝ}
-- given
  (h : r > 0) :
-- imply
  min (x * r) (y * r) = r * min x y := by
-- proof
  rw [mul_comm r]
  exact (min_mul_of_nonneg x y h.le).symm


-- created on 2019-08-18
