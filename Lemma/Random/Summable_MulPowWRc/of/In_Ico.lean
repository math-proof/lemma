import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
For `γ ∈ [0, 1)` the discounted series `∑ k, γ ^ k * ∫ z, Kf θ (clip) k z ∂(stageK θ y)` is summable
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (y : 𝒮) :
-- imply
  Summable (fun k =>
    γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
      ∂(M.stageK θ y)) := by
-- proof
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.env.R) M.env.R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R M.env.R z.1
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) ?_
  intro k
  have : IsProbabilityMeasure (M.stageK θ y) := inferInstance
  have h :=
    norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
      (Filter.Eventually.of_forall
        (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hclip hbound θ k).2)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg h₀.1 k)
  rwa [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at h


-- created on 2026-10-07
-- updated on 2026-11-14
