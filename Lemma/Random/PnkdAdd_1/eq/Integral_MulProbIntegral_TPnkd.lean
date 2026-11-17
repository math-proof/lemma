import Lemma.Random.Pnkd.eq.Integral
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
One-step recursion of the `n`-step state transition of the continuous-action model `M`:
`Pnkd θ (n+1) x y = ∫ u, π_θ(u | x) * ∫ y', T(dy' | x, u) * Pnkd θ n y' y du`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (n : ℕ)
  (sₜ y : 𝒮) :
-- imply
  M.Pnkd θ (n + 1) sₜ y =
    ∫ u, M.π[θ] sₜ u *
      (∫ y', M.Pnkd θ n y' y ∂(M.trans (sₜ, u)))
      ∂ReferenceMeasure.measure := by
-- proof
  rw [Pnkd.eq.Integral (M := M) θ (n + 1) sₜ y,
    WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ n sₜ]
  simp [Pnkd]


-- created on 2026-11-13
-- updated on 2026-11-16
