import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Real


/--
Every real function of a measurable finite-valued random variable is integrable: `Integrable (φ ∘ X)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
  {M : DensityModel Θ 𝒮 𝒜}
  {X : (ℕ → ℝ × 𝒮 × 𝒜) → B}
-- given
  (hX : Measurable X)
  (θ : Θ)
  (φ : B → ℝ) :
-- imply
  Integrable (fun ω => φ (X ω)) (M θ) := by
-- proof
  refine Integrable.of_bound (C := ∑ b, ‖φ b‖)
    ((StronglyMeasurable.of_discrete (f := φ)).comp_measurable hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun b => ‖φ b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)


-- created on 2026-10-07
-- updated on 2026-11-14
