import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusPressureDuality.Part3
open Finset Set SimpleGraph Filter Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexTorusPrimalPartitionSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorusPrimalPartitionSum_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < triHexTorusPrimalPartitionSum L p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalPartitionSum_pos L hp hp1 hq

/--
[triHexTorusDualPartitionSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorusDualPartitionSum_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pDual q : ℝ}
-- given
  (hp : 0 < pDual)
  (hp1 : pDual < 1)
  (hq : 0 < q) :
-- imply
  0 < triHexTorusDualPartitionSum L pDual q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualPartitionSum_pos L hp hp1 hq

/--
[triHexTorusDefectWeightedDualPartitionSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorusDefectWeightedDualPartitionSum_pos_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pDual q : ℝ}
-- given
  (hp : 0 < pDual)
  (hp1 : pDual < 1)
  (hq : 0 < q) :
-- imply
  0 < triHexTorusDefectWeightedDualPartitionSum L pDual q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefectWeightedDualPartitionSum_pos L hp hp1 hq

/--
[triHexTorus_partitionCorrection_ratio_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorus_partitionCorrection_ratio_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  1 ≤ triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q / triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ∧ triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q / triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ≤ q ^ 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_partitionCorrection_ratio_bounds L hp hp1 hq

/--
[triHexTorus_partitionCorrection_log_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorus_partitionCorrection_log_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  0 ≤ Real.log (triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q / triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ∧ Real.log (triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q / triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ≤ 2 * Real.log q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_partitionCorrection_log_bounds L hp hp1 hq

/--
[triHexTorus_partitionCorrection_logDensity_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorus_partitionCorrection_logDensity_tendsto_zero_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (triHexTorusPartitionCorrectionLogDensity p q) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_partitionCorrection_logDensity_tendsto_zero hp hp1 hq

/--
[triHexTorusPressureDualityResidual_eq_partitionCorrection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorusPressureDualityResidual_eq_partitionCorrection_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  triHexTorusPressureDualityResidual L p q = Real.log (triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q / triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) / (L ^ 2 : ℕ) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPressureDualityResidual_eq_partitionCorrection L hp hp1 hq

/--
[triHexTorusPressureDualityResidual_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean)
-/
@[path]
private lemma triHexTorusPressureDualityResidual_tendsto_zero_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n : ℕ => (by let L := n + 3 letI : Fact (2 < L) := ⟨by simp [L]⟩ exact triHexTorusPressureDualityResidual L p q : ℝ)) atTop (nhds (0 : ℝ)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPressureDualityResidual_tendsto_zero hp hp1 hq


-- created on 2026-10-23
