import Lemma.Random.ProbJoint.eq.Mul_Prob_Pr
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
Joint law of state and action in the continuous-action trajectory model,
written as an integral of the atom indicator:
`𝔼[1{s[t] = x ∧ a[t] = u}] = ℙ(s[t] = x) * π_θ(u | x) * μ({u})`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {t : ℕ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) ∂(M θ) =
    (M θ).real (s t ⁻¹' {sₜ}) * (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  have hA : MeasurableSet (a t ⁻¹' {aₜ}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton aₜ)
  have hSA : MeasurableSet (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) := hS.inter hA
  have hind :
    (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
      fun ω => if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0 := by
    funext ω
    by_cases hsx : s t ω = sₜ <;> by_cases hau : a t ω = aₜ <;>
      simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
  rw [← hind, integral_indicator_one hSA]
  apply ProbJoint.eq.Mul_Prob_Pr h₀


-- created on 2026-10-07
-- updated on 2026-11-18