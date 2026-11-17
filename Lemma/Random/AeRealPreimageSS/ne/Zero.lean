import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
almost surely every visited state is reachable
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
-- given
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M.traj θ), ∀ k, (M.traj θ).real (s k ⁻¹' {s k ω}) ≠ 0 := by
-- proof
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have e : {ω : ℕ → ℝ × 𝒮 × 𝒜 | ¬ (M.traj θ).real (s k ⁻¹' {s k ω}) ≠ 0} =
      ⋃ y ∈ {y : 𝒮 | (M.traj θ).real (s k ⁻¹' {y}) = 0}, s k ⁻¹' {y} := by
    ext ω; simp
  rw [e]
  exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun y hy =>
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hy


-- created on 2026-10-06
-- updated on 2026-11-17