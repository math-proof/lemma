import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : max a b < x) :
-- imply
  a < x := by
-- proof
  exact lt_of_le_of_lt (le_max_left a b) h


-- created on 2020-01-10
