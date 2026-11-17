import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Transition probabilities are nonnegative: `0 ≤ T(x, u, y)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
-- given
  (sₜ : 𝒮)
  (aₜ : 𝒜)
  (y : 𝒮) :
-- imply
  0 ≤ (M.trans (sₜ, aₜ)).toMeasure.real {y} := by
-- proof
  apply measureReal_nonneg


-- created on 2026-10-07
-- updated on 2026-11-16