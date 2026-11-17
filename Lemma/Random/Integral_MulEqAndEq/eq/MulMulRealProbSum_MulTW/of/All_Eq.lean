import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.ProbJoint.eq.Mul_Prob_Pr
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * r[t+j+1]] = ℙ(s[t] = x) * π_θ(u | x) * μ({u}) * ∫ y, (∫ w, Kf θ clip j w ∂(stageK θ y)) ∂T(x, u)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t j : ℕ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * r (t + (j + 1)) ω ∂(M.traj θ) =
    (M.traj θ).real (s t ⁻¹' {sₜ}) * (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) *
      ∫ y, (∫ w, M.Kf θ (fun z ↦ clip z.1 (-M.R) M.R) j w ∂(M.stageK θ y))
        ∂(M.trans (sₜ, aₜ)) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 ↦ clip z.1 (-M.R) M.R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hclipbound : ∀ z : ℝ × 𝒮 × 𝒜,
    ‖clip z.1 (-M.R) M.R‖ ≤ |M.R| :=
    fun z => NormClip.le.Abs_R M.R z.1
  have hGeq :
    (fun z : ℝ × 𝒮 × 𝒜 => if z.2.1 = sₜ ∧ z.2.2 = aₜ then (1:ℝ) else 0) =
      ((fun z : ℝ × 𝒮 × 𝒜 => z.2) ⁻¹' {(sₜ, aₜ)}).indicator (fun _ => (1:ℝ)) := by
    funext z
    if hz : z.2 = (sₜ, aₜ) then
      simp [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, hz]
    else
      have hzu : ¬(z.2.1 = sₜ ∧ z.2.2 = aₜ) := fun h' => hz (Prod.ext h'.1 h'.2)
      simp [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, hz, hzu]
  have hG : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => if z.2.1 = sₜ ∧ z.2.2 = aₜ then (1:ℝ) else 0) := by
    rw [hGeq]
    apply (stronglyMeasurable_const (b := (1:ℝ))).indicator
    exact measurable_snd (measurableSet_singleton (sₜ, aₜ))
  have hGbound : ∀ z : ℝ × 𝒮 × 𝒜,
    ‖(if z.2.1 = sₜ ∧ z.2.2 = aₜ then (1:ℝ) else 0)‖ ≤ (1:ℝ) := fun z => by
    if h : z.2.1 = sₜ ∧ z.2.2 = aₜ then
      simp [h]
    else
      simp [h]
  have hrc :
    ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) * r (t + (j + 1)) ω ∂(M.traj θ) =
      ∫ ω, (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) *
        clip (ω (t + (j + 1))).1 (-M.R) M.R ∂(M.traj θ) :=
    integral_congr_ae
      ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ (t + (j + 1))).mono
        fun ω h => by
          dsimp only
          rw [h])
  rw [hrc]
  rw [Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hclipbound hG hGbound θ t (j + 1)]
  have hKf : ∀ z,
      M.Kf θ (fun z ↦ clip z.1 (-M.R) M.R) (j + 1) z =
        ∫ y, (∫ w, M.Kf θ (fun z ↦ clip z.1 (-M.R) M.R) j w
          ∂(M.stageK θ y)) ∂(M.trans (z.2.1, z.2.2)) :=
    fun z =>
      Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hclip hclipbound θ j z
  have hfun :
    (fun ω =>
      (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) *
        M.Kf θ (fun z ↦ clip z.1 (-M.R) M.R) (j + 1) (ω t)) =
      fun ω =>
        (if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) *
          ∫ y, (∫ w, M.Kf θ (fun z ↦ clip z.1 (-M.R) M.R) j w
            ∂(M.stageK θ y)) ∂(M.trans (sₜ, aₜ)) := by
    funext ω
    if h : s t ω = sₜ ∧ a t ω = aₜ then
      have hz : (ω t).2 = (sₜ, aₜ) := Prod.ext h.1 h.2
      simp [h, hKf, hz]
    else
      simp [h]
  rw [hfun, integral_mul_const]
  have hS : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  have hA : MeasurableSet (a t ⁻¹' {aₜ}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton aₜ)
  have hSA : MeasurableSet (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) := hS.inter hA
  have hind :
    (fun ω => if s t ω = sₜ ∧ a t ω = aₜ then (1:ℝ) else 0) =
      (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) := by
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
  rw [hind, integral_indicator_one hSA, ProbJoint.eq.Mul_Prob_Pr (M := M) h₀ sₜ aₜ]


-- created on 2026-10-07
-- updated on 2026-11-16