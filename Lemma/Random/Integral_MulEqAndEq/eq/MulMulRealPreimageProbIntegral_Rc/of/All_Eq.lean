import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * r[t]] = ℙ(s[t] = x) * π_θ(u | x) * μ({u}) * 𝔼[clip | x, u]`
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * r t ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {sₜ}) * (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) *
      ∫ ρ, clip (ρ, sₜ, aₜ).1 (-R) R ∂(M.reward (sₜ, aₜ)) := by
-- proof
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-R) R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-R) R‖ ≤ |R| :=
    fun z => NormClip.le.Abs_R R z.1
  have hgu : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 =>
      (if z.2.2 = aₜ then (1:ℝ) else 0) * clip z.1 (-R) R) := by
    have hInd : StronglyMeasurable
      (fun z : ℝ × 𝒮 × 𝒜 => if z.2.2 = aₜ then (1:ℝ) else 0) := by
      have hEq :
        (fun z : ℝ × 𝒮 × 𝒜 => if z.2.2 = aₜ then (1:ℝ) else 0) =
          ({z : ℝ × 𝒮 × 𝒜 | z.2.2 = aₜ}).indicator 1 := by
        funext z
        by_cases h : z.2.2 = aₜ <;> simp [h, Set.indicator]
      rw [hEq]
      exact (stronglyMeasurable_const (b := (1:ℝ))).indicator
        (measurable_snd.snd (measurableSet_singleton aₜ))
    exact hInd.mul hclip
  have h₁ : ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * r t ω ∂(M θ) =
      ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) *
        clip (ω t).1 (-R) R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) hR θ t).mono
      fun ω h => by dsimp only; rw [h])
  have h₂ : ∀ ω,
    (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) *
      clip (ω t).1 (-R) R =
    (if s t ω = sₜ then (1:ℝ) else 0) *
      (fun z : ℝ × 𝒮 × 𝒜 =>
        (if z.2.2 = aₜ then (1:ℝ) else 0) * clip z.1 (-R) R) (ω t) := by
    intro ω
    have hs : s t ω = (ω t).2.1 := (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha : a t ω = (ω t).2.2 := (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    simp only [hs, ha]
    by_cases h1 : (ω t).2.1 = sₜ <;> by_cases h2 : (ω t).2.2 = aₜ <;> simp [h1, h2]
  have hinner :
    ∫ z, (if z.2.2 = aₜ then (1:ℝ) else 0) * clip z.1 (-R) R
      ∂(M.stageK θ sₜ) =
      M.π[θ] sₜ aₜ * μ.measure.real {aₜ} *
        ∫ ρ, clip (ρ, sₜ, aₜ).1 (-R) R ∂(M.reward (sₜ, aₜ)) := by
    rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hgu (LeNorm_Mul1.of.All_LeNorm
        (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.2 = aₜ)) hbound) θ sₜ]
    have hv : ∀ v,
      M.π[θ] sₜ v •
        ∫ ρ, (if v = aₜ then (1:ℝ) else 0) *
          clip (ρ, sₜ, v).1 (-R) R ∂(M.reward (sₜ, v)) =
      (if v = aₜ then (1:ℝ) else 0) * M.π[θ] sₜ v *
        ∫ ρ, clip (ρ, sₜ, aₜ).1 (-R) R ∂(M.reward (sₜ, aₜ)) := by
      intro v
      if hv : v = aₜ then
        subst hv
        simp [smul_eq_mul]
      else
        simp [hv, smul_eq_mul]
    simp_rw [hv, integral_mul_const]
    have hfun :
      (fun v => (if v = aₜ then (1:ℝ) else 0) * M.π[θ] sₜ v) =
        ({aₜ} : Set 𝒜).indicator (M.π[θ] sₜ) := by
      funext v
      by_cases hv : v = aₜ <;> simp [hv, Set.indicator]
    rw [hfun, integral_indicator (measurableSet_singleton aₜ),
      Measure.restrict_singleton, integral_smul_measure]
    simp [integral_dirac, smul_eq_mul, measureReal_def, mul_comm]
  rw [h₁]
  simp_rw [h₂]
  rw [Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    h₀ (M := M)
    (g := fun z =>
      (if z.2.2 = aₜ then (1:ℝ) else 0) * clip z.1 (-R) R)
    hgu
    (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.2 = aₜ)) hbound)
    θ t sₜ, hinner]
  ac_rfl


-- created on 2026-10-07
-- updated on 2026-11-18