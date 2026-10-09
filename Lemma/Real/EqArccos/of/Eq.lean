import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.arccos x = Real.arccos y :=
-- proof
  congr_arg Real.arccos h


-- created on 2022-01-20
