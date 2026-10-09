import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ≥ 0)
  (h : x < y) :
-- imply
  x * x < y * y := by
-- proof
  exact mul_self_lt_mul_self hx h


-- created on 2020-01-01
