import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ y)
  (h₁ : y > 0) :
-- imply
  Real.log x ≥ Real.log y :=
-- proof
  Real.log_le_log h₁ h₀


-- created on 2019-05-26
