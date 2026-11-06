import Def.Dynamics.PolicyTrajectory.ContinuousAction

/-!
# Retired: discrete Model value API (V0 / V / Q / Pn / P1)

These definitions moved onto DensityModel (Def.Dynamics.PolicyTrajectory.ContinuousAction):
* Model.V0 / Model.V -> DensityModel.V0 / DensityModel.V (tsum of gamma^k * Wkd)
* Model.Q / Model.Q0 -> DensityModel.Q / DensityModel.Q0
* Model.P1 / next-state densities -> DensityModel.P1kd (integral form; equals the Finset sum
  under [CountableMeasure A])

Convert a discrete Model with [CountableMeasure A] [Fintype A] via Model.toDensityModel,
then use DensityModel.IsConditionalProbability for GAE / GradExpect leaves.
-/
