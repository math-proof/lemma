import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * r[t]] = ℙ(s[t] = x) * π_θ(u | x) * μ({u}) * 𝔼[clip | x, u]`
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * (M.policy.prob θ x u * μ.measure.real {u}) *
      ∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u)) := by
-- proof
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.env.R) M.env.R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R M.env.R z.1
  have hgu : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 =>
      (if z.2.2 = u then (1:ℝ) else 0) * clip z.1 (-M.env.R) M.env.R) := by
    have hInd : StronglyMeasurable
      (fun z : ℝ × 𝒮 × 𝒜 => if z.2.2 = u then (1:ℝ) else 0) := by
      have hEq :
        (fun z : ℝ × 𝒮 × 𝒜 => if z.2.2 = u then (1:ℝ) else 0) =
          ({z : ℝ × 𝒮 × 𝒜 | z.2.2 = u}).indicator 1 := by
        funext z
        by_cases h : z.2.2 = u <;> simp [h, Set.indicator]
      rw [hEq]
      exact (stronglyMeasurable_const (b := (1:ℝ))).indicator
        (measurable_snd.snd (measurableSet_singleton u))
    exact hInd.mul hclip
  have h₁ : ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω ∂(M θ) =
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        clip (ω t).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ t).mono
      fun ω h => by dsimp only; rw [h])
  have h₂ : ∀ ω,
    (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      clip (ω t).1 (-M.env.R) M.env.R =
    (if s t ω = x then (1:ℝ) else 0) *
      (fun z : ℝ × 𝒮 × 𝒜 =>
        (if z.2.2 = u then (1:ℝ) else 0) * clip z.1 (-M.env.R) M.env.R) (ω t) := by
    intro ω
    have hs : s t ω = (ω t).2.1 := (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha : a t ω = (ω t).2.2 := (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    simp only [hs, ha]
    by_cases h1 : (ω t).2.1 = x <;> by_cases h2 : (ω t).2.2 = u <;> simp [h1, h2]
  have hinner :
    ∫ z, (if z.2.2 = u then (1:ℝ) else 0) * clip z.1 (-M.env.R) M.env.R
      ∂(M.stageK θ x) =
      M.policy.prob θ x u * μ.measure.real {u} *
        ∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u)) := by
    rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hgu (LeNorm_Mul1.of.All_LeNorm
        (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.2 = u)) hbound) θ x]
    have hv : ∀ v,
      M.policy.prob θ x v •
        ∫ ρ, (if v = u then (1:ℝ) else 0) *
          clip (ρ, x, v).1 (-M.env.R) M.env.R ∂(M.env.reward (x, v)) =
      (if v = u then (1:ℝ) else 0) * M.policy.prob θ x v *
        ∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u)) := by
      intro v
      if hv : v = u then
        subst hv
        simp [smul_eq_mul]
      else
        simp [hv, smul_eq_mul]
    simp_rw [hv, integral_mul_const]
    have hfun :
      (fun v => (if v = u then (1:ℝ) else 0) * M.policy.prob θ x v) =
        ({u} : Set 𝒜).indicator (M.policy.prob θ x) := by
      funext v
      by_cases hv : v = u <;> simp [hv, Set.indicator]
    rw [hfun, integral_indicator (measurableSet_singleton u),
      Measure.restrict_singleton, integral_smul_measure]
    simp [integral_dirac, smul_eq_mul, measureReal_def, mul_comm]
  rw [h₁]
  simp_rw [h₂]
  rw [Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    h₀ (M := M)
    (g := fun z =>
      (if z.2.2 = u then (1:ℝ) else 0) * clip z.1 (-M.env.R) M.env.R)
    hgu
    (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.2 = u)) hbound)
    θ t x, hinner]
  ac_rfl


-- created on 2026-10-07
-- updated on 2026-11-14
