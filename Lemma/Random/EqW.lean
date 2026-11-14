import Lemma.Random.EqMapStageK_12.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
`∫ z, f (s z) ∂(stageK θ y) = f y`: the `0`-step kernel expectation of a state function is the function itself.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : 𝒮 → ℝ}
-- given
  (h₀ : StronglyMeasurable f)
  (θ : Θ)
  (y : 𝒮) :
-- imply
  ∫ z, (f z.2.1) ∂(M.stageK θ y) = f y := by
-- proof
  have := M.env.reward_markov
  have hmap : (M.stageK θ y).map (fun z => z.2.1) = Measure.dirac y := by
    have h := EqMapStageK_12.of.All_EqWithDensity (M := M) θ (Measure.dirac y)
    rwa [Measure.dirac_bind (Kernel.measurable (M.stageK θ))] at h
  rw [← integral_map_of_stronglyMeasurable measurable_snd.fst h₀, hmap]
  apply integral_dirac' f y h₀


-- created on 2026-10-07
-- updated on 2026-11-14
