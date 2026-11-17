import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
An event of real probability `0` is null: `(M.traj θ).real B = 0 → M.traj θ B = 0`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {B : Set (ℕ → ℝ × 𝒮 × 𝒜)}
  {θ : Θ}
-- given
  (h : (M.traj θ).real B = 0) :
-- imply
  M.traj θ B = 0 :=
-- proof
  (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h


-- created on 2026-10-07
-- updated on 2026-11-17