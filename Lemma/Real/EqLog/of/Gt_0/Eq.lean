import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (_h_gt : x > 0)
  (h : x = y) :
-- imply
  Real.log x = Real.log y :=
-- proof
  congr_arg Real.log h


-- created on 2019-08-08
