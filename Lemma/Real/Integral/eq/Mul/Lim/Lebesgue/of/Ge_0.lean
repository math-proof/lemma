import Mathlib.MeasureTheory.Integral.Layercake
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  {μ : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
  (h₀ : MeasureTheory.Integrable f μ)
  (h₁ : 0 ≤ᵐ[μ] f) :
-- imply
  (∫ x, f x ∂μ) = ∫ t in Set.Ioi 0, μ.real {x | t ≤ f x} := by
-- proof
  apply MeasureTheory.Integrable.integral_eq_integral_meas_le h₀ h₁


-- created on 2026-10-11
-- updated on 2026-10-17
