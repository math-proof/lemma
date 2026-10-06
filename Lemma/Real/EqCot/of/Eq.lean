import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  Real.cot x = Real.cot y :=
-- proof
  congr_arg Real.cot h


-- created on 2022-01-20
