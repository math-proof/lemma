import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[path]
private lemma main
  {t x : ℝ}
-- given
  (h : 0 < x) :
-- imply
  t * Real.log x = Real.log (x ^ t) :=
-- proof
  (Real.log_rpow h t).symm


-- created on 2020-01-29
