import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h : x ≤ min a b) :
-- imply
  x ≤ a ∧ x ≤ b := by
-- proof
  exact le_min_iff.mp h


-- created on 2022-01-03
