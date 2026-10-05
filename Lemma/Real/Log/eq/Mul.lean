import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic


@[main]
private lemma main
  {b e : ℝ}
-- given
  (h : 0 < b) :
-- imply
  Real.log (b ^ e) = e * Real.log b := by
-- proof
  exact Real.log_rpow h e


-- created on 2023-04-16
