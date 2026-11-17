import Lemma.Random.ProbJoint.eq.Mul_Prob_Pr
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * φ(s[t], a[t])] = ℙ(s[t] = x) * π_θ(u | x) * μ({u}) * φ x u`
in the continuous-action trajectory model.
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
  (φ : 𝒮 → 𝒜 → ℝ) :
-- imply
  ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1:ℝ) else 0) * φ (ω t).2.1 (ω t).2.2 ∂(M.traj θ) =
    (M.traj θ).real (s t ⁻¹' {sₜ}) * (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) * φ sₜ aₜ := by
-- proof
  have h₂ : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
      (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1:ℝ) else 0) * φ (ω t).2.1 (ω t).2.2 =
        (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * φ sₜ aₜ := by
    intro ω
    have hs : s t ω = (ω t).2.1 := (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha : a t ω = (ω t).2.2 := (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    simp only [hs, ha]
    if h1 : (ω t).2.1 = sₜ then
      if h2 : (ω t).2.2 = aₜ then
        simp [h1, h2]
      else
        simp [h1, h2]
    else
      simp [h1]
  simp_rw [h₂]
  rw [integral_mul_const]
  have hS : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  have hA : MeasurableSet (a t ⁻¹' {aₜ}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton aₜ)
  have hSA : MeasurableSet (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) := hS.inter hA
  have hind :
    (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
      fun ω => if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0 := by
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
  rw [← hind, integral_indicator_one hSA, ProbJoint.eq.Mul_Prob_Pr (M := M) h₀ sₜ aₜ]


-- created on 2026-10-07
-- updated on 2026-11-17