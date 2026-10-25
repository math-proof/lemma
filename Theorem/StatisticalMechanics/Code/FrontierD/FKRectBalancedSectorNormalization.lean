/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBalancedSectorNormalization_le_one
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorNormalization R q ≤ 1 := by
  let A := R.width * R.height
  let s := Real.sqrt q
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by linarith)
  have hfinite := sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area
    R hq 0 (Nat.zero_le _)
  have hmul := mul_le_mul_of_nonneg_left hfinite (pow_nonneg hs.le A)
  unfold fkRectBalancedSectorNormalization
  dsimp [A, s] at hmul ⊢
  calc
    Real.sqrt q ^ (R.width * R.height) *
          (sixVertexTorusFixedChargePartitionSum R.medialTorus 0
              (Nat.zero_le _) (fkQgt4SixVertexWeight q) /
            fkRectCriticalReducedZ R q) ≤
        Real.sqrt q ^ (R.width * R.height) *
          (1 / Real.sqrt q) ^ (R.width * R.height) := hmul
    _ = 1 := by
      rw [one_div_pow, one_div]
      exact mul_inv_cancel₀
        (pow_ne_zero (R.width * R.height) hs.ne')

theorem fkRectBalancedSectorNormalization_mem_Ioc
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorNormalization R q ∈ Set.Ioc 0 1 :=
  ⟨fkRectBalancedSectorNormalization_pos R hq,
    fkRectBalancedSectorNormalization_le_one R hq⟩


theorem fkRectBalancedSectorNormalization_negLog_nonneg
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    0 ≤ -Real.log (fkRectBalancedSectorNormalization R q) := by
  rw [neg_nonneg]
  exact Real.log_nonpos
    (fkRectBalancedSectorNormalization_pos R hq).le
    (fkRectBalancedSectorNormalization_le_one R hq)


end
end StatMech.FrontierD
