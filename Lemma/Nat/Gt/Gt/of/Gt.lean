import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x y b : ℝ}
-- given
  (h : x > max y b) :
-- imply
  x > y ∧ x > b := by
-- proof
  exact max_lt_iff.mp h


-- created on 2019-07-18
