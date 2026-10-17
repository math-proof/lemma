import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x = y) :
-- imply
  Real.arcsin x⁻¹ = Real.arcsin y⁻¹ :=
-- proof
  congr_arg (fun t : ℝ => Real.arcsin t⁻¹) h₀


-- created on 2026-10-11
-- updated on 2026-10-17
