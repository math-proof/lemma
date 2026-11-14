import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
The state marginal sums to `1`: `∑ y, ℙ(s[t] = y) = 1`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∑ y, (M θ).real (s t ⁻¹' {y}) = 1 := by
-- proof
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
  have : IsProbabilityMeasure (M θ) := inferInstance
  have h : ∫ y, (1:ℝ) ∂((M θ).map (s t)) = 1 := by
    rw [integral_map (μ := M θ) hs.aemeasurable
      stronglyMeasurable_const.aestronglyMeasurable]
    rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  rw [integral_fintype Integrable.of_finite] at h
  simp only [smul_eq_mul, mul_one] at h
  refine (Finset.sum_congr rfl fun y _ => ?_).trans h
  rw [← map_measureReal_apply hs (measurableSet_singleton _)]


-- created on 2026-10-06
-- updated on 2026-11-14
