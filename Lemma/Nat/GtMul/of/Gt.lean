import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y k : ℝ}
-- given
  (h : x > y)
  (hk : k > 0) :
-- imply
  x * k > y * k := by
-- proof
  exact mul_lt_mul_of_pos_right h hk


-- created on 2026-09-27
