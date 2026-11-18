import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward `fun z ↦ clip z.1 (-R) R` is strongly measurable.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy]
-- given
  (R : ℝ) :
-- imply
  StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 ↦ clip z.1 (-R) R := by
-- proof
  unfold clip
  apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable


-- created on 2026-10-07
-- updated on 2026-11-18
