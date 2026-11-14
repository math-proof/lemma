import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
`∫ z, f z ∂(stageK θ x) = ∫ u, π_θ(u | x) * ∫ ρ, f (ρ, x, u) ∂(reward (x, u)) du`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (h₀ : StronglyMeasurable f)
  (h₁ : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (x : 𝒮) :
-- imply
  ∫ z, f z ∂(M.stageK θ x) =
    ∫ (u : 𝒜), (M.policy.prob θ x u * ∫ ρ, f (ρ, x, u) ∂(M.env.reward (x, u)))
      ∂μ.measure := by
-- proof
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity (M := M) h₀ h₁ θ]
  simp [smul_eq_mul]


-- created on 2026-10-07
-- updated on 2026-11-14
