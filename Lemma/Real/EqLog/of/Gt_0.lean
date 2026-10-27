import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {r : ℝ}
-- given
  (h₀ : r > 0)
  (z : ℝ) :
-- imply
  Real.log (r ^ z) = z * Real.log r :=
-- proof
  Real.log_rpow h₀ z


-- created on 2023-04-16
