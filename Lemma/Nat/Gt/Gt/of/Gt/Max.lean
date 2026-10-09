import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x a b : ℝ}
-- given
  (h : x > max a b) :
-- imply
  x > a ∧ x > b := by
-- proof
  exact max_lt_iff.mp h


-- created on 2022-01-03
