import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : x > max a b) :
-- imply
  x > a ∧ x > b := by
-- proof
  exact max_lt_iff.mp h


-- created on 2019-08-04
