import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
open MeasureTheory PolicyGradient


/--
`(x, u) ↦ rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` is jointly measurable (the reward is a kernel on `S × A`).
-/
@[main]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A} :
-- imply
  Measurable (fun z : S × A => M.rkd z.1 z.2) := by
-- proof
  have := M.env.reward_markov
  exact (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.reward)
    (f := fun z : (S × A) × ℝ => max (-M.env.R) (min M.env.R z.2))
    (measurable_const.max (measurable_const.min measurable_snd)).stronglyMeasurable).measurable


-- created on 2026-10-07
