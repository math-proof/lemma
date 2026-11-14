import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Def.Order.Miscellaneous
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
The closed-form expected reward `Wkd θ k x` is the kernel expectation of the clamped reward:
`Wkd θ k x = ∫ z, Kf θ (fun z ↦ clip z.1 (-R) R) k z ∂(stageK θ x)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (k : ℕ)
  (x : 𝒮) :
-- imply
  M.Wkd θ k x =
    ∫ z, M.Kf θ (fun z => clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ x) := by
-- proof
  have hf : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.env.R) M.env.R) := by
    unfold clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R _ _
  induction k generalizing x with
  | zero =>
    change ∫ u, M.policy.prob θ x u * M.rkd x u ∂ReferenceMeasure.measure =
      ∫ z, clip z.1 (-M.env.R) M.env.R ∂(M.stageK θ x)
    rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ x]
    simp [smul_eq_mul, DensityModel.rkd]
  | succ k ih =>
    have := M.env.trans_markov
    rw [WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ k x]
    change (∫ u, M.policy.prob θ x u *
        (∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) ∂ReferenceMeasure.measure) = _
    congr 1
    funext u
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => ih y)


-- created on 2026-11-13
