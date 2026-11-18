import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`𝔼[φ(s[t])] = ∑ y, ℙ(s[t] = y) • φ y` under the trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜]
  [NormedAddCommGroup ℰ]
  [NormedSpace ℝ ℰ]
  [CompleteSpace ℰ]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (φ : 𝒮 → ℰ) :
-- imply
  ∫ ω, φ (s t ω) ∂(M θ) = ∑ y, (M θ).real (s t ⁻¹' {y}) • φ y := by
-- proof
  have e := integral_map (μ := M θ) (Random.Measurable.of.All_Eq.snd.fst h₀ t).aemeasurable
    (f := φ) StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine e.symm.trans ?_
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_measureReal_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t) (measurableSet_singleton _)]


-- created on 2026-10-06
-- updated on 2026-11-18