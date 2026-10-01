import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y r : ℝ}
-- given
  (h : r < 0) :
-- imply
  max (r * x) (r * y) = min x y * r := by
-- proof
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy, max_eq_left (mul_le_mul_of_nonpos_left hxy h.le), mul_comm]
  · rw [min_eq_right hxy, max_eq_right (mul_le_mul_of_nonpos_left hxy h.le), mul_comm]


-- created on 2020-01-19
