/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusComparison.Part2
open Finset Set SimpleGraph Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorusPrimalPartitionSum_pos
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < triHexTorusPrimalPartitionSum L p q := by
  unfold triHexTorusPrimalPartitionSum
  exact Finset.sum_pos
    (fun omega _ => FK.fkWeight_pos _ hp hp1 hq omega)
    Finset.univ_nonempty

theorem triHexTorusDualPartitionSum_pos
    (L : ℕ) [Fact (2 < L)] {pDual q : ℝ}
    (hp : 0 < pDual) (hp1 : pDual < 1) (hq : 0 < q) :
    0 < triHexTorusDualPartitionSum L pDual q := by
  unfold triHexTorusDualPartitionSum
  exact Finset.sum_pos
    (fun omega _ => FK.fkWeight_pos _ hp hp1 hq
      (triHexTorusDualConfig L omega))
    Finset.univ_nonempty

theorem triHexTorusDefectWeightedDualPartitionSum_pos
    (L : ℕ) [Fact (2 < L)] {pDual q : ℝ}
    (hp : 0 < pDual) (hp1 : pDual < 1) (hq : 0 < q) :
    0 < triHexTorusDefectWeightedDualPartitionSum L pDual q := by
  unfold triHexTorusDefectWeightedDualPartitionSum
  exact Finset.sum_pos (fun omega _ => mul_pos
    (FK.fkWeight_pos _ hp hp1 hq (triHexTorusDualConfig L omega))
    (zpow_pos hq _)) Finset.univ_nonempty


theorem triHexTorus_partitionCorrection_ratio_bounds
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    1 ≤ triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q /
        triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ∧
      triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q /
        triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ≤ q ^ 2 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  have hD := triHexTorusDualPartitionSum_pos L hpDual hpDual1 hq0
  have hbounds := triHexTorus_defectWeighted_partition_bounds L hp hp1 hq
  constructor
  · rw [le_div_iff₀ hD]
    simpa using hbounds.1
  · rw [div_le_iff₀ hD]
    simpa [mul_comm] using hbounds.2


theorem triHexTorus_partitionCorrection_log_bounds
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    0 ≤ Real.log
        (triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q /
          triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ∧
      Real.log
          (triHexTorusDefectWeightedDualPartitionSum L
              (BeffaraDC.dualParam p q) q /
            triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ≤
        2 * Real.log q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  have hW := triHexTorusDefectWeightedDualPartitionSum_pos
    L hpDual hpDual1 hq0
  have hD := triHexTorusDualPartitionSum_pos L hpDual hpDual1 hq0
  have hratioPos : 0 <
      triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q /
        triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q :=
    div_pos hW hD
  have hb := triHexTorus_partitionCorrection_ratio_bounds L hp hp1 hq
  constructor
  · exact Real.log_nonneg hb.1
  · have hq2 : 0 < q ^ 2 := pow_pos hq0 _
    have hmono := Real.strictMonoOn_log.monotoneOn
      hratioPos hq2 hb.2
    simpa [Real.log_pow] using hmono


end PeriodicPlanar
end FK
end StatMech
