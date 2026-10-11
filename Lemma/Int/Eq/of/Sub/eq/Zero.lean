import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : 0 = a - b) :
-- imply
  a = b := by
-- proof
  exact sub_eq_zero.mp h.symm


-- created on 2018-05-09
