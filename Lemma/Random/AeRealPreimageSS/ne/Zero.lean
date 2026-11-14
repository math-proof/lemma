import Def.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
almost surely every visited state is reachable
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
-- given
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, (M θ).real (s k ⁻¹' {s k ω}) ≠ 0 := by
-- proof
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have e : {ω : ℕ → ℝ × 𝒮 × 𝒜 | ¬ (M θ).real (s k ⁻¹' {s k ω}) ≠ 0} =
      ⋃ y ∈ {y : 𝒮 | (M θ).real (s k ⁻¹' {y}) = 0}, s k ⁻¹' {y} := by
    ext ω; simp
  rw [e]
  exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun y hy =>
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hy


-- created on 2026-10-06
-- updated on 2026-11-14
