import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
`𝔼[1{s[t] = x} * r[t+j]] = ℙ(s[t] = x) * W θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j x`
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t j : ℕ)
  (x : 𝒮) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) *
      ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j z ∂(M.stageK θ x) := by
-- proof
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.env.R) M.env.R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R M.env.R z.1
  have h₂ : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) *
        clip (ω (t + j)).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ (t + j)).mono
      fun ω h => by dsimp only; rw [h])
  rw [h₂]
  apply Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    h₀ (M := M) hclip hbound


-- created on 2026-10-07
-- updated on 2026-11-14
