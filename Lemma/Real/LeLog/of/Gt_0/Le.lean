import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : 0 < x)
  (h₁ : x ≤ y) :
-- imply
  Real.log x ≤ Real.log y := by
-- proof
  apply Real.log_le_log h₀ h₁


-- created on 2019-08-24
-- updated on 2026-10-17
