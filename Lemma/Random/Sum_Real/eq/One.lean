import Def.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
The initial state distribution of the trajectory model sums to `1`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] :
-- imply
  ∑ x, M.init.toMeasure.real {x} = 1 := by
-- proof
  rw [sum_measureReal_singleton]
  simp


-- created on 2026-10-06
-- updated on 2026-11-16