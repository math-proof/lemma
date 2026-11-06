import Def.Dynamics.PolicyTrajectory.ContinuousAction

/-!
# Retired: finite-action closed forms on Model

The closed forms Model.rk / Model.Wk / Model.Vk / Model.Qk / Model.P1k that lived here
are superseded by DensityModel.rkd / Wkd / V0 / Q0 / P1kd in
Def.Dynamics.PolicyTrajectory.ContinuousAction.

For a countable discrete (or finite-action) policy, take [CountableMeasure A] and convert:
* Policy.toDensityPolicy -- sum_eq_one becomes integral_eq_one vs Measure.count
* Model.toDensityModel -- same env, density policy; use DensityModel.V0 / Wkd /
  DensityModel.IsConditionalProbability

Continuous-state + finite-action is the same special case (counting measure on A).
-/
