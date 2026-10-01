import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {a b : ℝ}
-- given
  (h : a = b) :
-- imply
  a - b = 0 := by
-- proof
  exact sub_eq_zero.mpr h


-- created on 2021-06-26
