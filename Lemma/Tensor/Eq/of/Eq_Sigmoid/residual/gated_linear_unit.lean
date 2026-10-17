import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  (1 + Real.exp (-x))⁻¹ * y + (1 + Real.exp x)⁻¹ * y = y := by
-- proof
  have hsig : (1 + Real.exp (-x))⁻¹ + (1 + Real.exp x)⁻¹ = 1 := by
    field_simp
    ring_nf
    rw [Real.exp_neg]
    field_simp
    ring
  calc
    _ = ((1 + Real.exp (-x))⁻¹ + (1 + Real.exp x)⁻¹) * y := by
      ring
    _ = 1 * y := by
      rw [hsig]
    _ = y := by
      ring


-- created on 2026-10-11
-- updated on 2026-10-17
