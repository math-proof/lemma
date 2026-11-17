import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Def.Order.Miscellaneous
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The closed-form expected reward `Wkd θ k x` is the kernel expectation of the clamped reward:
`Wkd θ k x = ∫ z, Kf θ (fun z ↦ clip z.1 (-R) R) k z ∂(stageK θ x)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (k : ℕ)
  (sₜ : 𝒮) :
-- imply
  M.Wkd θ k sₜ =
    ∫ z, M.Kf θ (fun z => clip z.1 (-M.R) M.R) k z ∂(M.stageK θ sₜ) := by
-- proof
  have hf : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.R) M.R) := by
    unfold clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.R) M.R‖ ≤ |M.R| :=
    fun z => NormClip.le.Abs_R _ _
  induction k generalizing sₜ with
  | zero =>
    change ∫ u, M.π[θ] sₜ u * M.rkd sₜ u ∂ReferenceMeasure.measure =
      ∫ z, clip z.1 (-M.R) M.R ∂(M.stageK θ sₜ)
    rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ sₜ]
    simp [smul_eq_mul, Model.rkd]
  | succ k ih =>
    rw [WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ k sₜ]
    change (∫ u, M.π[θ] sₜ u *
        (∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))) ∂ReferenceMeasure.measure) = _
    congr 1
    funext u
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => ih y)


-- created on 2026-11-13
-- updated on 2026-11-17
