import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : 0 < x)
  (h₁ : x < y) :
-- imply
  Real.log x < Real.log y := by
-- proof
  exact Real.log_lt_log h₀ h₁


-- created on 2023-04-16
