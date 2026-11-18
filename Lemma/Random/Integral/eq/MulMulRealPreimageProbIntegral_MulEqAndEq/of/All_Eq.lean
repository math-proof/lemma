import Lemma.Random.ProbJoint.eq.Mul_Prob_Pr
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[f | s[t] = x, a[t] = u] = (ℙ(s[t] = x) * π_θ(u | x) * μ({u}))⁻¹ * 𝔼[1{s[t] = x ∧ a[t] = u} * f]`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮)
  (aₜ : 𝒜)
  (f : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}] =
    ((M θ).real (s t ⁻¹' {sₜ}) * (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}))⁻¹ *
      ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * f ω ∂(M θ) := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  have hA : MeasurableSet (a t ⁻¹' {aₜ}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton aₜ)
  have hB : MeasurableSet (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) := hS.inter hA
  have hP : (M θ).real (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) =
      (M θ).real (s t ⁻¹' {sₜ}) * (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) :=
    ProbJoint.eq.Mul_Prob_Pr (M := M) h₀ sₜ aₜ
  have hind :
    (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}).indicator f =
      fun ω => (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * f ω := by
    funext ω
    if hsx : s t ω = sₜ then
      if hau : a t ω = aₜ then
        simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
      else
        simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
    else
      simp [hsx, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul, hP, hind]


-- created on 2026-10-07
-- updated on 2026-11-18