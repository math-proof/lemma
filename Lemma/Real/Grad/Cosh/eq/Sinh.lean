import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- imply
  : deriv Real.cosh x = Real.sinh x :=
-- proof
  congrFun Real.deriv_cosh x


-- created on 2023-11-26
