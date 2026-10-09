import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- imply
  : deriv Real.sinh x = Real.cosh x :=
-- proof
  congrFun Real.deriv_sinh x


-- created on 2023-11-26
