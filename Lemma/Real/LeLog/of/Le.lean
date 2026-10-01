import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : x ≤ y) :
-- imply
  Real.log x ≤ Real.log y :=
-- proof
  Real.log_le_log h₀ h₁


-- created on 2019-08-23
