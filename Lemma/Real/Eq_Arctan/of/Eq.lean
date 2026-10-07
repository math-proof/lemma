import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : Real.arctan x = Real.arctan y) :
-- imply
  x = y :=
-- proof
  Real.arctan_injective h


-- created on 2022-01-23
