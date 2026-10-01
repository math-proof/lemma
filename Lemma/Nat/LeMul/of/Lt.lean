import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y k : ℝ}
-- given
  (h : x < y)
  (hk : k ≥ 0) :
-- imply
  x * k ≤ y * k := by
-- proof
  exact mul_le_mul_of_nonneg_right h.le hk


-- created on 2019-11-24
