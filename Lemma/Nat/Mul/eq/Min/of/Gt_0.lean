import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x y : ℝ}
-- given
  (h : a > 0) :
-- imply
  min x y * a = min (x * a) (y * a) := by
-- proof
  exact min_mul_of_nonneg _ _ h.le


-- created on 2019-08-19
