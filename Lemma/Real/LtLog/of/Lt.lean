import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (h : x < y) :
-- imply
  Real.log x < Real.log y := by
-- proof
  exact Real.log_lt_log hx h


-- created on 2022-04-01
