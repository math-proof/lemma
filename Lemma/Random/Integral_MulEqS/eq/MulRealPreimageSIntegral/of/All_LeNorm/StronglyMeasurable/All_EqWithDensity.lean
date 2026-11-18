import Lemma.Random.Integral.eq.Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulIte.eq.MulKroneckerDeltaIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Def.Analysis.SpecialFunctions.TensorFunctions
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Nat Random Real


/--
`𝔼[1{s[t] = x} * g(ω[t])] = ℙ(s[t] = x) * ∫ z, g z ∂(stageK θ x)` for a bounded strongly measurable `g`
on the continuous-action trajectory model (`Model`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {g : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮) :
-- imply
  ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * g (ω t) ∂(M θ) =
    (M θ).real (s t ⁻¹' {sₜ}) * ∫ z, g z ∂(M.stageK θ sₜ) := by
-- proof
  have hst : ∀ ω, s t ω = (ω t).2.1 := fun ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  have hm : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => (if z.2.1 = sₜ then (1:ℝ) else 0) * g z) :=
    ((StronglyMeasurable.of_discrete (f := (fun y : 𝒮 => if y = sₜ then (1:ℝ) else 0))).comp_measurable measurable_snd.fst).mul hg
  have : IsProbabilityMeasure ((M θ).map (s t)) :=
    inferInstance
  have e1 : ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * g (ω t) ∂(M θ) =
      ∫ z, (if z.2.1 = sₜ then (1:ℝ) else 0) * g z ∂((M θ).map (fun ω => ω t)) := by
    rw [integral_map (measurable_pi_apply t).aemeasurable hm.aestronglyMeasurable]; simp only [hst]
  rw [e1, Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity h₀,
    Integral.eq.Integral.of.All_LeNorm.StronglyMeasurable hm
      (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.1 = sₜ)) hC)]
  simp_rw [Integral_MulIte.eq.MulKroneckerDeltaIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hg hC θ sₜ]
  have h₂ : ∀ y', (KroneckerDelta y' sₜ : ℝ) * ∫ z, g z ∂(M.stageK θ y') =
      (KroneckerDelta y' sₜ : ℝ) * ∫ z, g z ∂(M.stageK θ sₜ) := by
    intro y'; by_cases h : y' = sₜ <;> simp [h, KroneckerDelta]
  simp_rw [h₂]
  rw [integral_mul_const]
  congr 1
  have h₃ : (fun y' : 𝒮 => (KroneckerDelta y' sₜ : ℝ)) = ({sₜ} : Set 𝒮).indicator 1 := by
    funext y'; by_cases h : y' = sₜ <;> simp [h, KroneckerDelta]
  rw [h₃, integral_indicator_one (measurableSet_singleton sₜ), measureReal_def, measureReal_def,
    Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t) (measurableSet_singleton sₜ)]


-- created on 2026-11-04
-- updated on 2026-11-18