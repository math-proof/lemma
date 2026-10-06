import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : |x| = 0) :
-- imply
  x = 0 :=
-- proof
  abs_eq_zero.mp h


-- created on 2018-03-15
