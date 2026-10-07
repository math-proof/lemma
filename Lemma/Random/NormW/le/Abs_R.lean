import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The kernel expectation of the clamped reward is bounded: `‖W θ rc j y‖ ≤ |R|`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (j : ℕ)
  (y : S) :
-- imply
  ‖M.W θ M.rc j y‖ ≤ |M.env.R| := by
-- proof
  have h := norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
    (Filter.Eventually.of_forall (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ j).2)
  show ‖∫ z, M.Kf θ M.rc j z ∂(M.stageK θ y)‖ ≤ _
  simpa using h


-- created on 2026-10-07
