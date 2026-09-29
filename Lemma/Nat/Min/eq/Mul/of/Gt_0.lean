import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y r : ℝ}
-- given
  (h : r > 0) :
-- imply
  min (x * r) (y * r) = min x y * r := by
-- proof
  exact (min_mul_of_nonneg x y h.le).symm


-- created on 2026-09-27
