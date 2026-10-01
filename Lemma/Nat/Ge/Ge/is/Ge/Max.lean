import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ} :
-- imply
  x ≥ a ∧ x ≥ b ↔ x ≥ max a b := by
-- proof
  exact max_le_iff.symm


-- created on 2026-09-27
