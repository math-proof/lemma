import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
import Mathlib.Probability.Kernel.MeasurableIntegral
open MeasureTheory PolicyGradient


/--
`(x, u) ↦ rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` is jointly measurable (the reward is a kernel on `S × A`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A} :
-- imply
  Measurable (fun z : S × A => M.rkd z.1 z.2) := by
-- proof
  have := M.env.reward_markov
  simp only [DensityModel.rkd]
  apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.reward)
    (f := fun z : (S × A) × ℝ => clip z.2 (-M.env.R) M.env.R) _).measurable
  unfold clip
  apply ((measurable_snd.max measurable_const).min measurable_const).stronglyMeasurable


-- created on 2026-10-07
-- updated on 2026-10-26
