import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic


@[main]
private lemma main
  {r : ℝ}
-- given
  (h₀ : r > 0)
  (z : ℝ) :
-- imply
  Real.log (r ^ z) = z * Real.log r :=
-- proof
  Real.log_rpow h₀ z


-- created on 2026-09-26
