import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingPeriodicProduct
open StatMech StatMech.FrontierA


/--
[prod_one_sub_quantumIsingPeriodicRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingPeriodicProduct.lean)
-/
@[path]
private lemma prod_one_sub_quantumIsingPeriodicRoot_eq
  {n : Nat}
  {z : Complex}
-- given
  (hn : n ≠ 0) :
-- imply
  (∏ j ∈ Finset.range n, (1 - z * quantumIsingPeriodicRoot n j)) = 1 - z ^ n := by
-- proof
  apply StatMech.FrontierA.prod_one_sub_quantumIsingPeriodicRoot n hn z

/--
[prod_sub_cos_quantumIsingPeriodicAngle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingPeriodicProduct.lean)
-/
@[path]
private lemma prod_sub_cos_quantumIsingPeriodicAngle_eq
  {n : Nat}
  {r : Real}
-- given
  (hn : n ≠ 0)
  (hr : 0 < r) :
-- imply
  (∏ j ∈ Finset.range n, ((r + r⁻¹) / 2 - Real.cos (quantumIsingPeriodicAngle n j))) = (r / 2) ^ n * (1 - r⁻¹ ^ n) ^ 2 := by
-- proof
  apply StatMech.FrontierA.prod_sub_cos_quantumIsingPeriodicAngle n hn r hr

/--
[prod_sub_cos_periodic_le_antiperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingPeriodicProduct.lean)
-/
@[path]
private lemma prod_sub_cos_periodic_le_antiperiodic_eq
  {n : Nat}
  {r : Real}
-- given
  (hn : n ≠ 0)
  (hr : 1 ≤ r) :
-- imply
  (∏ j ∈ Finset.range n, ((r + r⁻¹) / 2 - Real.cos (quantumIsingPeriodicAngle n j))) ≤ ∏ j ∈ Finset.range n, ((r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j)) := by
-- proof
  apply StatMech.FrontierA.prod_sub_cos_periodic_le_antiperiodic n hn r hr


-- created on 2026-10-23
