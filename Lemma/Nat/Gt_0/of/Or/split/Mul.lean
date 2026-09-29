import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0) :
-- imply
  x * y > 0 := by
-- proof
  exact mul_pos_iff.mpr h


-- created on 2026-09-27
