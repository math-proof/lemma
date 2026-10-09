import sympy.Basic


@[path]
private lemma main
  {x y r : ℝ}
-- given
  (h : r < 0) :
-- imply
  min (x * r) (y * r) = r * max x y := by
-- proof
  rcases le_total x y with hxy | hxy
  ·
    rw [max_eq_right hxy, min_eq_right (mul_le_mul_of_nonpos_right hxy h.le), mul_comm]
  ·
    rw [max_eq_left hxy, min_eq_left (mul_le_mul_of_nonpos_right hxy h.le), mul_comm]


-- created on 2020-01-26
