import Lemma.Random.Kf.eq.Integral.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
One more step of the iterated kernel expectation:
`Kf θ f (j+1) z = ∫ y, (∫ w, Kf θ f j w ∂(stageK θ y)) ∂(trans (z.s, z.a))`.
Continuous-action counterpart of
`Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  M.Kf θ f (j + 1) z =
    ∫ y, (∫ w, M.Kf θ f j w ∂(M.stageK θ y)) ∂(M.env.trans (z.2.1, z.2.2)) := by
-- proof
  have := M.env.trans_markov
  rw [Kf.eq.Integral.All_EqWithDensity (M := M) (f := f) θ j z]
  have hK : M.K θ z = M.stageK θ ∘ₘ M.env.trans (z.2.1, z.2.2) := by
    rw [DensityModel.K, Kernel.comp_apply, Kernel.comap_apply]
  have hKf :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ j
  rw [hK, Integral.eq.Integral.of.All_LeNorm.StronglyMeasurable hKf.1 hKf.2]


-- created on 2026-11-13
