import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x ≥ y) :
-- imply
  x - y ≥ 0 := by
-- proof
  exact sub_nonneg.mpr h


-- created on 2026-09-27
