import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : Real.arcsin x⁻¹ = Real.arcsin y⁻¹) :
-- imply
  Real.arcsin x⁻¹ = Real.arcsin y⁻¹ :=
-- proof
  h₀


-- created on 2022-01-23
-- updated on 2026-10-26
