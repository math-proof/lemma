import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b t : ℝ}
-- given
  (h : a < b) :
-- imply
  a + t < b + t := by
-- proof
  apply add_lt_add_left h t


-- created on 2021-05-27
