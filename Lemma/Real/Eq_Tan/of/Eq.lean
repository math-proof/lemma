import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : Real.tan x = Real.tan y) :
-- imply
  Real.tan x = Real.tan y :=
-- proof
  h


-- created on 2022-01-23
-- updated on 2026-10-17
