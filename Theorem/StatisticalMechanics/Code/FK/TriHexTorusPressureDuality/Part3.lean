/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusComparison.Part2
import Def.StatisticalMechanics.Code.FK.TriHexTorusPressureDuality.Part2
open Finset Set SimpleGraph Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorusPressureDualityResidual_eq_partitionCorrection
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexTorusPressureDualityResidual L p q =
      Real.log
        (triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q /
          triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q) /
        (L ^ 2 : ℕ) := by
  let pDual := BeffaraDC.dualParam p q
  let m := (triangularTorusGraph L).edgeFinset.card
  let v := Nat.card (TorusSite L)
  let PZ := triHexTorusPrimalPartitionSum L p q
  let DZ := triHexTorusDualPartitionSum L pDual q
  let WZ := triHexTorusDefectWeightedDualPartitionSum L pDual q
  let b := p / (1 - pDual)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual : 0 < pDual := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 : pDual < 1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  have hb : 0 < b := div_pos hp (sub_pos.mpr hpDual1)
  have hP : 0 < PZ := triHexTorusPrimalPartitionSum_pos L hp hp1 hq0
  have hD : 0 < DZ := triHexTorusDualPartitionSum_pos L hpDual hpDual1 hq0
  have hW : 0 < WZ :=
    triHexTorusDefectWeightedDualPartitionSum_pos L hpDual hpDual1 hq0
  have hpart := triHexTorus_partition_duality_defectWeighted L hp hp1 hq0
  have hpart' : PZ * q ^ (m + 1) = b ^ m * q ^ v * WZ := by
    simpa only [PZ, DZ, WZ, b, pDual, m, v] using hpart
  have hlog := congrArg Real.log hpart'
  rw [Real.log_mul hP.ne' (pow_pos hq0 _).ne', Real.log_pow,
    Real.log_mul (mul_pos (pow_pos hb _) (pow_pos hq0 _)).ne' hW.ne',
    Real.log_mul (pow_pos hb _).ne' (pow_pos hq0 _).ne',
    Real.log_pow, Real.log_pow] at hlog
  have hres :
      Real.log PZ + (m + 1 : ℝ) * Real.log q -
          ((m : ℝ) * Real.log b + (v : ℝ) * Real.log q + Real.log DZ) =
        Real.log (WZ / DZ) := by
    rw [Real.log_div hW.ne' hD.ne']
    push_cast at hlog
    linarith
  unfold triHexTorusPressureDualityResidual
  dsimp only
  change (Real.log PZ + (m + 1 : ℝ) * Real.log q -
      ((m : ℝ) * Real.log b + (v : ℝ) * Real.log q + Real.log DZ)) /
        ((L ^ 2 : ℕ) : ℝ) = _
  rw [hres]


theorem triHexTorusPressureDualityResidual_tendsto_zero
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => (by
      let L := n + 3
      letI : Fact (2 < L) := ⟨by simp [L]⟩
      exact triHexTorusPressureDualityResidual L p q : ℝ))
      atTop (nhds (0 : ℝ)) := by
  apply (triHexTorus_partitionCorrection_logDensity_tendsto_zero
    hp hp1 hq).congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by simp [L]⟩
  exact (triHexTorusPressureDualityResidual_eq_partitionCorrection
    L hp hp1 hq).symm

end PeriodicPlanar
end FK
end StatMech
