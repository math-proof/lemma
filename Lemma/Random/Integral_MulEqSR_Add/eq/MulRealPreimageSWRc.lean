import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * r[t+j]] = ℙ(s[t] = x) * W θ (fun z ↦ clip z.1 (-R) R) j x`
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ)
  (t j : ℕ)
  (sₜ : 𝒮) :
-- imply
  ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {sₜ}) *
      ∫ z, M.Kf θ (fun z ↦ clip z.1 (-R) R) j z ∂(M.stageK θ sₜ) := by
-- proof
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-R) R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-R) R‖ ≤ |R| :=
    fun z => NormClip.le.Abs_R R z.1
  have h₂ : ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * r (t + j) ω ∂(M θ) =
      ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) *
        clip (ω (t + j)).1 (-R) R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) hR θ (t + j)).mono
      fun ω h => by dsimp only; rw [h])
  rw [h₂]
  apply Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    h₀ (M := M) hclip hbound


-- created on 2026-10-07
-- updated on 2026-11-18