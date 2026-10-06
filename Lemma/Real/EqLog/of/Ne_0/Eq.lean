import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h_ne : x ≠ 0)
  (h : x = y) :
-- imply
  Real.log x = Real.log y :=
-- proof
  congr_arg Real.log h


-- created on 2021-08-02
