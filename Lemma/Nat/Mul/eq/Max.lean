import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {t x y : ℝ}
-- given
  (ht : t > 0) :
-- imply
  t * max x y = max (t * x) (t * y) := by
-- proof
  exact mul_max_of_nonneg _ _ ht.le


-- created on 2026-09-27
