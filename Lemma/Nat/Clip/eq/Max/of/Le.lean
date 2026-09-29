import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h : a ≤ b) :
-- imply
  min (max x a) b = max (min x b) a := by
-- proof
  rw [max_comm (min x b) a, max_min_distrib_left, max_eq_right h, max_comm]


-- created on 2026-09-27
