import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Recursion of the time-homogeneous kernel expectation:
`∫ z, Kf θ f (j+1) z ∂(stageK θ x) = ∫ u, π_θ(u | x) * ∫ y, (∫ z, Kf θ f j z ∂(stageK θ y)) ∂(trans (x, u)) du`.
Continuous-action counterpart of
`Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ)
  (sₜ : 𝒮) :
-- imply
  ∫ z, M.Kf θ f (j + 1) z ∂(M.stageK θ sₜ) =
    ∫ u, M.π[θ] sₜ u *
      (∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u)))
      ∂ReferenceMeasure.measure := by
-- proof
  have h :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ (j + 1)
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) h.1 h.2 θ sₜ]
  simp_rw [Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hf hC θ j, smul_eq_mul]
  congr 1
  funext u
  simp


-- created on 2026-11-13
-- updated on 2026-11-17
