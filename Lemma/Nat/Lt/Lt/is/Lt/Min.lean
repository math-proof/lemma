import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ} :
-- imply
  x < a ∧ x < b ↔ x < min a b := by
-- proof
  exact lt_min_iff.symm


-- created on 2026-09-27
