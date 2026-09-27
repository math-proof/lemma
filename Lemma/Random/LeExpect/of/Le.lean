import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f g : Ω → ℝ}
-- given
  (h₀ : ∀ ω, f ω ≤ g ω)
  (h₁ : Integrable f μ)
  (h₂ : Integrable g μ) :
-- imply
  ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ :=
-- proof
  integral_mono h₁ h₂ h₀


-- created on 2026-09-26
