import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.coth x = Real.cosh x / Real.sinh x := by
-- proof
  rw [Real.coth, Real.tanh_eq_sinh_div_cosh, one_div, inv_div]


-- created on 2023-11-26
-- updated on 2026-10-26
