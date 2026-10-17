import Lemma.Real.Coth.eq.Div
import Lemma.Real.Square.Cosh.eq.Add.Square.Sinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.functions.elementary.hyperbolic
import sympy.Basic
open Real


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.sinh x ≠ 0) :
-- imply
  Real.csch x ^ 2 = Real.coth x ^ 2 - 1 := by
-- proof
  rw [Coth.eq.Div]
  simp only [Real.csch]
  field_simp [h]
  linarith [Square.Cosh.eq.Add.Square.Sinh x]


-- created on 2023-11-26
-- updated on 2026-10-17
