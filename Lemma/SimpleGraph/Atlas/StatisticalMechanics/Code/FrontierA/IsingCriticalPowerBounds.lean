import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalPowerBounds
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[coordinate_natAbs_le_criticalIsingSupRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma coordinate_natAbs_le_criticalIsingSupRadius_eq
  {d : Nat}
  {z : Site d}
  {i : Fin d} :
-- imply
  (z i).natAbs <= criticalIsingSupRadius z := by
-- proof
  apply StatMech.FrontierA.coordinate_natAbs_le_criticalIsingSupRadius z i

/--
[criticalIsingSupRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma criticalIsingSupRadius_pos_eq
  {d : Nat}
  {z : Site d}
-- given
  (hz : z ≠ Percolation.origin d) :
-- imply
  0 < criticalIsingSupRadius z := by
-- proof
  apply StatMech.FrontierA.criticalIsingSupRadius_pos z hz

/--
[mem_boxSV_vbF_criticalIsingSupRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma mem_boxSV_vbF_criticalIsingSupRadius_eq
  {d : Nat}
  {z : Site d}
-- given
  (hz : z ≠ Percolation.origin d) :
-- imply
  z ∈ boxSV_vbF d (criticalIsingSupRadius z) := by
-- proof
  apply StatMech.FrontierA.mem_boxSV_vbF_criticalIsingSupRadius z hz

/--
[currentContinuityFreeTwoPoint_eq_origin_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_eq_origin_sub_eq
  {d : Nat}
  {beta : Real}
  {x y : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  currentContinuityFreeTwoPoint d beta x y = currentContinuityFreeTwoPoint d beta (Percolation.origin d) (y - x) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_eq_origin_sub beta hbeta x y

/--
[currentContinuityFreeTwoPoint_le_one_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_le_one_of_ne_eq
  {d : Nat}
  {beta : Real}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hd : 1 <= d)
  (hxy : x ≠ y) :
-- imply
  currentContinuityFreeTwoPoint d beta x y <= 1 := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_le_one_of_ne beta hbeta hd x y hxy

/--
[exists_criticalFreeTwoPoint_shell_le_power_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma exists_criticalFreeTwoPoint_shell_le_power_all_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ (r : Nat), 1 <= r -> ∀ x ∈ boxSV_vbF d r, currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <= C / (r : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeTwoPoint_shell_le_power_all hd

/--
[exists_criticalFreeTwoPoint_shell_ge_power_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma exists_criticalFreeTwoPoint_shell_ge_power_all_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ c : Real, 0 < c ∧ ∀ (r : Nat), 1 <= r -> ∀ x ∈ boxSV_vbF d r, c / (r : Real) ^ (d - 1) <= currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeTwoPoint_shell_ge_power_all hd

/--
[exists_criticalFreeTwoPoint_shell_powerBounds_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma exists_criticalFreeTwoPoint_shell_powerBounds_all_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ c C : Real, 0 < c ∧ c < C ∧ ∀ (r : Nat), 1 <= r -> ∀ x ∈ boxSV_vbF d r, c / (r : Real) ^ (d - 1) <= currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x ∧ currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <= C / (r : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.exists_criticalFreeTwoPoint_shell_powerBounds_all hd

/--
[criticalIsingTwoPoint_powerBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalPowerBounds.lean)
-/
@[path]
private lemma criticalIsingTwoPoint_powerBounds_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ c C : Real, 0 < c ∧ c < C ∧ ∀ (x y : Site d), x ≠ y -> c / (criticalIsingSupRadius (y - x) : Real) ^ (d - 1) <= currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) x y ∧ currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) x y <= C / (criticalIsingSupRadius (y - x) : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.criticalIsingTwoPoint_powerBounds hd


-- created on 2026-10-23
