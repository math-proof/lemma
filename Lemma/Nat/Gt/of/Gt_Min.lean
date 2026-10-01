import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : min a b > x) :
-- imply
  a > x := by
-- proof
  exact lt_of_lt_of_le h (min_le_left a b)


-- created on 2019-08-04
