/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusComparison.Part2
import Def.StatisticalMechanics.Code.FK.TriHexTorusPressureDuality
open Finset Set SimpleGraph Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorus_partitionCorrection_logDensity_tendsto_zero
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (triHexTorusPartitionCorrectionLogDensity p q)
      atTop (nhds 0) := by
  let C : ℝ := 2 * Real.log q
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.log_nonneg hq)
  have hub : ∀ n : ℕ,
      triHexTorusPartitionCorrectionLogDensity p q n ≤
        C / ((n + 1 : ℕ) : ℝ) := by
    intro n
    let L := n + 3
    letI : Fact (2 < L) := ⟨by simp [L]⟩
    have hlog :=
      (triHexTorus_partitionCorrection_log_bounds L hp hp1 hq).2
    have hden0 : 0 ≤ ((L ^ 2 : ℕ) : ℝ) := by positivity
    have hsmall0 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hden : ((n + 1 : ℕ) : ℝ) ≤ ((L ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 1 ≤ (n + 3) ^ 2 by nlinarith)
    unfold triHexTorusPartitionCorrectionLogDensity
    dsimp only
    calc
      Real.log
          (triHexTorusDefectWeightedDualPartitionSum L
              (BeffaraDC.dualParam p q) q /
            triHexTorusDualPartitionSum L
              (BeffaraDC.dualParam p q) q) /
          ((L ^ 2 : ℕ) : ℝ) ≤ C / ((L ^ 2 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hlog hden0
      _ ≤ C / ((n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hC hsmall0 hden
  have hupper : Tendsto
      (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (Filter.tendsto_add_atTop_nat 1)
  apply squeeze_zero
  · intro n
    let L := n + 3
    letI : Fact (2 < L) := ⟨by simp [L]⟩
    unfold triHexTorusPartitionCorrectionLogDensity
    dsimp only
    exact div_nonneg
      (triHexTorus_partitionCorrection_log_bounds L hp hp1 hq).1
      (by positivity)
  · exact hub
  · exact hupper


end PeriodicPlanar
end FK
end StatMech
