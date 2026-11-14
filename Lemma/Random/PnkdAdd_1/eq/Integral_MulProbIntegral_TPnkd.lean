import Lemma.Random.Pnkd.eq.Integral
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
One-step recursion of the `n`-step state transition of the continuous-action model `M`:
`Pnkd θ (n+1) x y = ∫ u, π_θ(u | x) * ∫ y', T(dy' | x, u) * Pnkd θ n y' y du`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : 𝒮) :
-- imply
  M.Pnkd θ (n + 1) x y =
    ∫ u, M.policy.prob θ x u *
      (∫ y', M.Pnkd θ n y' y ∂(M.env.trans (x, u)))
      ∂ReferenceMeasure.measure := by
-- proof
  have := M.env.trans_markov
  rw [Pnkd.eq.Integral (M := M) θ (n + 1) x y,
    WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ n x]
  simp [Pnkd]


-- created on 2026-11-13
