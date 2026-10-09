import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x * y > 0) :
-- imply
  (x < 0 ∧ y < 0) ∨ (x > 0 ∧ y > 0) := by
-- proof
  exact (mul_pos_iff.mp h).symm


-- created on 2026-10-03
