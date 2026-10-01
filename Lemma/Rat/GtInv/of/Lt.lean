import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (hx : x > 0)
  (h : x < a) :
-- imply
  1 / x > 1 / a := by
-- proof
  exact one_div_lt_one_div_of_lt hx h


-- created on 2019-12-29
