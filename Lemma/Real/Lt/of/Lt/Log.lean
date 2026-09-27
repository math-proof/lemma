import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : 0 < y)
  (h₁ : Real.log x < Real.log y) :
-- imply
  x < y := by
-- proof
  if h : 0 < x then
    exact (Real.log_lt_log_iff h h₀).mp h₁
  else
    linarith


-- created on 2026-09-26
