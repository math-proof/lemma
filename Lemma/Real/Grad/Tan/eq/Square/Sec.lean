import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (x : ℝ) :
-- imply
  deriv Real.tan x = Real.sec x ^ 2 := by
-- proof
  rw [Real.deriv_tan, Real.sec, div_pow, one_pow]


-- created on 2023-11-26
-- updated on 2026-10-26
