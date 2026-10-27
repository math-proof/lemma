import Mathlib.Analysis.Complex.Trigonometric
import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.tanh x = Real.sinh x / Real.cosh x :=
  -- proof
  Real.tanh_eq_sinh_div_cosh x


-- created on 2023-11-26
