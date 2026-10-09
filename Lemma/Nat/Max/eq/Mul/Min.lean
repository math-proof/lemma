import sympy.Basic


@[path]
private lemma main
  {x y r : ℝ}
-- given
  (h : r < 0) :
-- imply
  max (x * r) (y * r) = r * min x y := by
-- proof
  rcases le_total x y with hxy | hxy
  ·
    rw [min_eq_left hxy, max_eq_left (by nlinarith), mul_comm]
  ·
    rw [min_eq_right hxy, max_eq_right (by nlinarith), mul_comm]


-- created on 2020-01-24
