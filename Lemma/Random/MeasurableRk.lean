import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
open MeasureTheory PolicyGradient


/--
`x ↦ rk x u = 𝔼[r[t] | s[t] = x, a[t] = u]` is measurable (the reward is a kernel on `S × A`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (u : A) :
-- imply
  Measurable (fun x => M.rk x u) := by
-- proof
  have := M.env.reward_markov
  apply (StronglyMeasurable.integral_kernel_prod_right (κ := M.env.reward.comap (fun x => (x, u)) (by fun_prop))
    (f := fun (_ : S) (ρ : ℝ) => max (-M.env.R) (min M.env.R ρ)) _).measurable
  apply (measurable_const.max (measurable_const.min measurable_snd)).stronglyMeasurable


-- created on 2026-10-07
