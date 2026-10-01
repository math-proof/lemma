import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ} :
-- imply
  x ≥ max a b ↔ x ≥ a ∧ x ≥ b := by
-- proof
  exact max_le_iff


-- created on 2026-09-27
