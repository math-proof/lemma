import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.arcsin x = Real.arcsin y :=
-- proof
  congr_arg Real.arcsin h


-- created on 2022-01-20
