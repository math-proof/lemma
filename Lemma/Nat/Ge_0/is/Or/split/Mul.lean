import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x * y ≥ 0 ↔ x ≥ 0 ∧ y ≥ 0 ∨ x ≤ 0 ∧ y ≤ 0 := by
-- proof
  exact mul_nonneg_iff


-- created on 2026-09-27
