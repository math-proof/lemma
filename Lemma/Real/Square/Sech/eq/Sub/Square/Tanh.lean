import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Def.Analysis.SpecialFunctions.Hyperbolic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sech x ^ 2 = 1 - Real.tanh x ^ 2 := by
-- proof
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Real.sech]
  field_simp [(Real.cosh_pos x).ne']
  linarith [Real.cosh_sq_sub_sinh_sq x]


-- created on 2023-11-26
-- updated on 2026-10-26
