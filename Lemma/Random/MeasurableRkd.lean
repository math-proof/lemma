import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Mathlib.Probability.Kernel.MeasurableIntegral
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient


/--
`(x, u) ↦ rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` is jointly measurable (the reward is a kernel on `𝒮 × 𝒜`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (R : ℝ) :
-- imply
  Measurable (fun z : 𝒮 × 𝒜 => M.rkd R z.1 z.2) := by
-- proof
  simp only [Model.rkd]
  apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.rewardK)
    (f := fun z : (𝒮 × 𝒜) × ℝ => clip z.2 (-R) R) _).measurable
  unfold clip
  apply ((measurable_snd.max measurable_const).min measurable_const).stronglyMeasurable


-- created on 2026-10-07
-- updated on 2026-11-18
