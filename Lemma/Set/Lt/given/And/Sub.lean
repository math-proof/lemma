import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b t : ℝ}
-- given
  (h : a < b) :
-- imply
  a - t < b - t := by
-- proof
  apply sub_lt_sub_right h t


-- created on 2021-05-28
