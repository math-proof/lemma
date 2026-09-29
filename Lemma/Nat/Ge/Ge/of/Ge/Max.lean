import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h : x ≥ max a b) :
-- imply
  x ≥ a ∧ x ≥ b := by
-- proof
  exact max_le_iff.mp h


-- created on 2026-09-27
