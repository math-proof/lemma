import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hy : 0 < y)
  (h : x > y) :
-- imply
  Real.log x > Real.log y :=
-- proof
  Real.log_lt_log hy h


-- created on 2022-03-31
-- updated on 2022-04-01
