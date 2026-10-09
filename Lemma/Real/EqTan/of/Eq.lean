import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.tan x = Real.tan y :=
-- proof
  congr_arg Real.tan h


-- created on 2021-09-27
