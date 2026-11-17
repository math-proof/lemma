import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The kernel expectation of the clamped reward is bounded:
`‖∫ z, Kf θ (fun z ↦ clip z.1 (-M.R) M.R) j z ∂(stageK θ y)‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (j : ℕ)
  (y : 𝒮) :
-- imply
  ‖∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.R) M.R) j z ∂(M.stageK θ y)‖ ≤ |M.R| := by
-- proof
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.R) M.R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.R) M.R‖ ≤ |M.R| :=
    fun z => NormClip.le.Abs_R M.R z.1
  have : IsProbabilityMeasure (M.stageK θ y) := inferInstance
  have h :=
    norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
      (Filter.Eventually.of_forall
        (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hclip hbound θ j).2)
  rwa [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at h


-- created on 2026-10-07
-- updated on 2026-11-17