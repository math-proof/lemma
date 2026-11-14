import Lemma.Random.Pnkd.eq.Integral
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
`Pnkd θ 0 x y = 1{x = y}`: the `0`-step state transition of the continuous-action model `M` is the identity.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (x y : 𝒮) :
-- imply
  M.Pnkd θ 0 x y = if x = y then 1 else 0 := by
-- proof
  have := M.env.reward_markov
  rw [Pnkd.eq.Integral (M := M) θ 0 x y]
  change ∫ z, (if z.2.1 = y then (1:ℝ) else 0) ∂(M.stageK θ x) = _
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ x]
  have hinter : ∀ u, ∫ ρ, (if x = y then (1:ℝ) else 0) ∂(M.env.reward (x, u)) =
      if x = y then 1 else 0 := by
    intro u
    simp
  simp_rw [hinter, smul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy, M.policy.integral_eq_one]
  · simp [hxy]


-- created on 2026-11-13
