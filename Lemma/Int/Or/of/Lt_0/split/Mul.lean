import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x * y < 0) :
-- imply
  x > 0 ∧ y < 0 ∨ x < 0 ∧ y > 0 := by
-- proof
  exact mul_neg_iff.mp h


-- created on 2026-09-27
