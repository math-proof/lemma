import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.arctan x = Real.arctan y :=
-- proof
  congr_arg Real.arctan h


-- created on 2022-01-20
