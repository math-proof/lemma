import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : Real.sin x ≠ 0)
  (h₁ : Real.cos x ≠ 0) :
-- imply
  Real.cot x * Real.tan x = 1 := by
-- proof
  simp [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, h₀, h₁]


-- created on 2023-10-03
