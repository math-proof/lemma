import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ≥ 0)
  (h : x < y) :
-- imply
  x * x < y * y := by
-- proof
  exact mul_self_lt_mul_self hx h


-- created on 2026-09-27
