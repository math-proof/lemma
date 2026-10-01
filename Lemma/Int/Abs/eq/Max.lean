import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  |x| = max x (-x) := by
-- proof
  exact abs_eq_max_neg


-- created on 2026-09-27
