import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x = y) :
-- imply
  Real.arccos x⁻¹ = Real.arccos y⁻¹ :=
-- proof
  congr_arg (fun t : ℝ => Real.arccos t⁻¹) h₀


-- created on 2022-01-23
-- updated on 2026-10-26
