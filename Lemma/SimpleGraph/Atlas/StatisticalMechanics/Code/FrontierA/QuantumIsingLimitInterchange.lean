import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingLimitInterchange
open Filter StatMech StatMech.FrontierA


/--
[quantumIsing_tendsto_of_uniform_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLimitInterchange.lean)
-/
@[path]
private lemma quantumIsing_tendsto_of_uniform_cylinder_bound_eq
  {trotterThermodynamic finiteQuantum : ℕ → ℝ}
  {finiteTrotter : ℕ → ℕ → ℝ}
  {freeEnergy : ℝ}
-- given
  (hfinite : ∀ L, Tendsto (finiteTrotter L) atTop (nhds (finiteQuantum L)))
  (hquantum : Tendsto finiteQuantum atTop (nhds freeEnergy))
  (huniform : ∀ L n, |trotterThermodynamic n - finiteTrotter L n| ≤ 1 / (2 * ((L : ℝ) + 1))) :
-- imply
  Tendsto trotterThermodynamic atTop (nhds freeEnergy) := by
-- proof
  apply StatMech.FrontierA.quantumIsing_tendsto_of_uniform_cylinder_bound trotterThermodynamic finiteQuantum finiteTrotter freeEnergy hfinite hquantum huniform


-- created on 2026-10-23
