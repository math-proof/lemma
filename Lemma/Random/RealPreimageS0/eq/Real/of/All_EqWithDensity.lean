import Lemma.Random.EqMapStageK_12.of.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
The law of `s[0]` under the continuous-action trajectory model is the initial distribution:
`ℙ(s[0] = x) = init {x}`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  (M.traj θ).real (s 0 ⁻¹' {sₜ}) = M.init.toMeasure.real {sₜ} := by
-- proof
  have hs : s 0 = fun ω ↦ (ω 0).2.1 := funext fun ω ↦ (congrArg (·.2.1) (congrFun (h₀ 0) ω)).symm
  have h : (M.traj θ).map (s 0) = ((M.traj θ).map (fun ω => ω 0)).map (fun z => z.2.1) := by
    rw [hs, Measure.map_map measurable_snd.fst (measurable_pi_apply 0)]; rfl
  rw [measureReal_def, ← Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h₀ 0) (measurableSet_singleton sₜ), h,
    Map.eq.BindStageK.of.All_EqWithDensity, EqMapStageK_12.of.All_EqWithDensity, measureReal_def]


-- created on 2026-11-13
-- updated on 2026-11-17
