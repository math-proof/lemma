import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : max a b ≤ x) :
-- imply
  a ≤ x ∧ b ≤ x := by
-- proof
  exact max_le_iff.mp h


-- created on 2019-11-29
