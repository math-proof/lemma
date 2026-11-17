import Lemma.Random.Pnkd.eq.Integral
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`Pnkd θ 0 x y = 1{x = y}`: the `0`-step state transition of the continuous-action model `M` is the identity.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (sₜ y : 𝒮) :
-- imply
  M.Pnkd θ 0 sₜ y = if sₜ = y then 1 else 0 := by
-- proof
  rw [Pnkd.eq.Integral (M := M) θ 0 sₜ y]
  change ∫ z, (if z.2.1 = y then (1:ℝ) else 0) ∂(M.stageK θ sₜ) = _
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ sₜ]
  have hinter : ∀ u, ∫ ρ, (if sₜ = y then (1:ℝ) else 0) ∂(M.reward (sₜ, u) : Measure ℝ) =
      if sₜ = y then 1 else 0 := by
    intro u
    simp
  simp_rw [hinter, smul_eq_mul]
  by_cases hxy : sₜ = y
  · simp [hxy]
    convert hStoch.integral_eq_one θ y
  · simp [hxy]


-- created on 2026-11-13
-- updated on 2026-11-16
