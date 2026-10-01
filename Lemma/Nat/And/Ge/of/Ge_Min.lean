import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : min a b ≥ x) :
-- imply
  a ≥ x ∧ b ≥ x := by
-- proof
  exact le_min_iff.mp h


-- created on 2019-06-08
