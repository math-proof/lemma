import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y r : ℝ}
-- given
  (h : r > 0) :
-- imply
  max (x * r) (y * r) = max x y * r := by
-- proof
  exact (max_mul_of_nonneg _ _ h.le).symm


-- created on 2026-09-27
