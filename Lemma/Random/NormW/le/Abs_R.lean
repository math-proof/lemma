import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
import sympy.Basic
import Lemma.Random.NormRc.le.AbsR
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The kernel expectation of the clamped reward is bounded:
`‖∫ z, Kf θ rc j z ∂(stageK θ y)‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (j : ℕ)
  (y : S) :
-- imply
  let rc (z : ℝ × S × A) : ℝ := clip z.1 (-M.env.R) M.env.R
  ‖∫ z, M.Kf θ rc j z ∂(M.stageK θ y)‖ ≤ |M.env.R| := by
-- proof
  intro rc
  have h := norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
    (Filter.Eventually.of_forall (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.AbsR (M := M)) θ j).2)
  simpa using h


-- created on 2026-10-07
-- updated on 2026-10-11
