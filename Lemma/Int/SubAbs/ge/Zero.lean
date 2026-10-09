import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  |x| - x ≥ 0 := by
-- proof
  exact sub_nonneg.mpr (le_abs_self x)


-- created on 2019-09-15
