import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y r : ℝ}
-- given
  (hr : r > 0) :
-- imply
  max (x * r) (y * r) = r * max x y := by
-- proof
  rw [← max_mul_of_nonneg _ _ hr.le, mul_comm]


-- created on 2019-08-17
