import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.cos x ≠ 0) :
-- imply
  Real.tan x ^ 2 = Real.sec x ^ 2 - 1 := by
-- proof
  rw [Real.tan_eq_sin_div_cos]
  simp only [Real.sec]
  field_simp [h]
  linarith [Real.sin_sq_add_cos_sq x]


-- created on 2023-10-03
-- updated on 2026-10-26
