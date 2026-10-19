import Lemma.Real.Coth.eq.Div
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.sinh x ≠ 0) :
-- imply
  Real.cosh x = Real.coth x * Real.sinh x := by
-- proof
  rw [Coth.eq.Div]
  field_simp [h]


-- created on 2023-11-26
-- updated on 2026-10-17
