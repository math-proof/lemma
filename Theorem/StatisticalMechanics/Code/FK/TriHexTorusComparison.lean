/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Def.StatisticalMechanics.Code.FK.TriHexTorusComparison
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorus_topologicalCorrection_bounds
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L)))
    {q : ℝ} (hq : 1 ≤ q) :
    1 ≤ q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega) ∧
      q ^ triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) ≤ q ^ 2 := by
  rcases triHexTorusDefect_openSub_classified L omega with h | h | h
  · rw [h]
    rw [zpow_zero]
    exact ⟨le_rfl, one_le_pow₀ hq⟩
  · rw [h]
    rw [zpow_one]
    refine ⟨hq, ?_⟩
    have hq0 : 0 ≤ q := zero_le_one.trans hq
    simpa [pow_two] using mul_le_mul_of_nonneg_right hq hq0
  · rw [h]
    rw [zpow_ofNat]
    exact ⟨one_le_pow₀ hq, le_rfl⟩


theorem triHexTorus_topologicalCorrection_log_bound
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L)))
    {q : ℝ} (hq : 1 ≤ q) :
    |Real.log (q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega))| ≤
      2 * Real.log q := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
  rcases triHexTorusDefect_openSub_classified L omega with h | h | h
  · rw [h]
    rw [zpow_zero, Real.log_one, abs_zero]
    exact mul_nonneg (by norm_num) hlog
  · rw [h]
    rw [zpow_one, abs_of_nonneg hlog]
    linarith
  · rw [h]
    rw [zpow_ofNat, Real.log_pow]
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hlog)]
    norm_num


end PeriodicPlanar
end FK
end StatMech
