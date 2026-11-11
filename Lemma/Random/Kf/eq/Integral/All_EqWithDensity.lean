import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


/--
`Kf θ f (j + 1) z = ∫ w, Kf θ f j w ∂(K θ z)` (bridge past the `𝔼` sugar on `DensityModel.Kf`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
-- given
  (θ : Θ)
  (j : ℕ)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  M.Kf θ f (j + 1) z = ∫ w, M.Kf θ f j w ∂(M.K θ z) := by
-- proof
  have : IsProbabilityMeasure (M.K θ z) := inferInstance
  have : PSpace (M.K θ z) (id : ℝ × 𝒮 × 𝒜 → ℝ × 𝒮 × 𝒜) :=
    ⟨measurable_id.aemeasurable⟩
  change Expectation.ofRV (M.K θ z) id (M.Kf θ f j) = _
  simp only [Expectation.ofRV, expectation_real, Measure.map_id]


-- created on 2026-10-20
