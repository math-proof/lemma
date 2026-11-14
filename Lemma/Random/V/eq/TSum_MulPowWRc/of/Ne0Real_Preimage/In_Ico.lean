import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS.of.All_EqWithDensity
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
On a reachable state (`ℙ(s[t] = x) ≠ 0`) of the continuous-action trajectory model:
`V θ γ t x = ∑' k, γ ^ k * W θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k x`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let V (θ : Θ) (t : ℕ) (x : 𝒮) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x);
  V θ t x = ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
    ∂(M.stageK θ x) := by
-- proof
  intro Vθ
  dsimp only [Vθ]
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 ↦ clip z.1 (-M.env.R) M.env.R) := by
    unfold clip
    apply
      ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hclipbound : ∀ z : ℝ × 𝒮 × 𝒜,
      ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R M.env.R z.1
  have hGx : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => if z.2.1 = x then (1:ℝ) else 0) :=
    (StronglyMeasurable.of_discrete
      (f := fun y' : 𝒮 => if y' = x then (1:ℝ) else 0)).comp_measurable
      measurable_snd.fst
  have hGxbound : ∀ z : ℝ × 𝒮 × 𝒜,
      ‖if z.2.1 = x then (1:ℝ) else 0‖ ≤ (1:ℝ) :=
    fun z => by
      if hz' : z.2.1 = x then
        simp [hz']
      else
        simp [hz']
  have hSW : ∀ k,
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + k) ω ∂(M θ) =
        (M θ).real (s t ⁻¹' {x}) *
          ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
            ∂(M.stageK θ x) := by
    intro k
    have hrc :
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + k) ω ∂(M θ) =
        ∫ ω, (if s t ω = x then (1:ℝ) else 0) *
          clip (ω (t + k)).1 (-M.env.R) M.env.R ∂(M θ) :=
      integral_congr_ae
        ((MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ (t + k)).mono
          fun ω h => by
            dsimp only
            rw [h])
    have hK :=
      StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hclip hclipbound θ k
    rw [hrc,
      Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hclip hclipbound hGx hGxbound θ t k,
      Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        h₁ (M := M) hK.1 hK.2 θ t x]
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hs : Measurable (s t) :=
    Random.Measurable.of.All_Eq.snd.fst h₁ t
  have hfG : Measurable
    (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hmap : (M θ).map (s t) {x} ≠ 0 := by
    rwa [Measure.map_apply hs (measurableSet_singleton x),
      ← measureReal_ne_zero_iff]
  simp only [Expectation.asRV_process]
  rw [Expectation.condEval_eq_integral hpR hs hfG hmap]
  show ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x}] = _
  rw [Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
    (M := M) h₀ h₁ θ (s t ⁻¹' {x}) t]
  congr 1
  funext k
  rw [Integral.eq.MulRealPreimageSIntegral_MulEqS.of.All_EqWithDensity h₁,
    hSW k, inv_mul_cancel_left₀ hP]


-- created on 2026-10-07
-- updated on 2026-11-14
