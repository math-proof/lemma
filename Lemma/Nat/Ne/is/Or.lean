import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  x ≠ y ↔ x > y ∨ x < y := by
-- proof
  rw [ne_iff_lt_or_gt]
  exact Or.comm


-- created on 2026-09-27
