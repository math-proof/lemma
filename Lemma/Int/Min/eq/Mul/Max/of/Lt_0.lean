import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y r : ℝ}
-- given
  (h : r < 0) :
-- imply
  min (r * x) (r * y) = max x y * r := by
-- proof
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, min_eq_right (mul_le_mul_of_nonpos_left hxy h.le), mul_comm]
  · rw [max_eq_left hxy, min_eq_left (mul_le_mul_of_nonpos_left hxy h.le), mul_comm]


-- created on 2021-10-02
