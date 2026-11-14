import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


/--
Conditional integral as a normalized integral: `∫ f ∂(μ[|B]) = μ(B)⁻¹ * ∫ 1_B * f ∂μ`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {B : Set (ℕ → ℝ × 𝒮 × 𝒜)}
-- given
  (hB : MeasurableSet B)
  (θ : Θ)
  (f : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|B] = ((M θ).real B)⁻¹ * ∫ ω, B.indicator 1 ω * f ω ∂(M θ) := by
-- proof
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul]
  congr 1
  congr 1
  funext ω
  by_cases h : ω ∈ B <;> simp [h]


-- created on 2026-10-07
-- updated on 2026-11-14
