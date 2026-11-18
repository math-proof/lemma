import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward is bounded by the reward bound:
`‖clip z.1 (-R) R‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy]
-- given
  (R : ℝ)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  ‖clip z.1 (-R) R‖ ≤ |R| := by
-- proof
  rw [Real.norm_eq_abs, abs_le, clip]
  constructor
  ·
    apply le_min
    ·
      apply (neg_le_neg (le_abs_self _)).trans
      apply le_max_right
    ·
      apply neg_abs_le
  ·
    apply (min_le_right _ _).trans
    apply le_abs_self


-- created on 2026-10-07
-- updated on 2026-11-18
