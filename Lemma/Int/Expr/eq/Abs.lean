import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ≥ 0) :
-- imply
  x = |x| := by
-- proof
  exact (abs_of_nonneg h).symm


-- created on 2026-09-27
