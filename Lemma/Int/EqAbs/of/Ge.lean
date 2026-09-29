import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≥ y) :
-- imply
  |x - y| = x - y := by
-- proof
  exact abs_of_nonneg (sub_nonneg.mpr h)


-- created on 2026-09-27
