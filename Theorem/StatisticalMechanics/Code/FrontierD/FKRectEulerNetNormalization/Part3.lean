/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBalancedSectorShare_mem_Ioc
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorShare R q ∈ Set.Ioc 0 1 := by
  constructor
  · exact div_pos (fkRectBalancedSectorNormalization_pos R hq)
      (fkRectAllSectorNormalization_pos R hq)
  · exact (div_le_one (fkRectAllSectorNormalization_pos R hq)).2
      (fkRectBalancedSectorNormalization_le_allSectorNormalization R hq)


theorem fkRectBalancedSectorNormalization_eq_share_mul_all
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorNormalization R q =
      fkRectBalancedSectorShare R q * fkRectAllSectorNormalization R q := by
  unfold fkRectBalancedSectorShare
  rw [div_mul_cancel₀]
  exact (fkRectAllSectorNormalization_pos R hq).ne'


theorem fkRectBalancedSectorShare_eq_sixVertexRatio
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorShare R q =
      sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q) /
        sixVertexTorusArrowPartitionSum R.medialTorus
          (fkQgt4SixVertexWeight q) := by
  unfold fkRectBalancedSectorShare fkRectBalancedSectorNormalization
    fkRectAllSectorNormalization
  have harea : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
    positivity
  have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R (by linarith)).ne'
  have hfull : sixVertexTorusArrowPartitionSum R.medialTorus
      (fkQgt4SixVertexWeight q) ≠ 0 := by
    intro hzero
    have hall := fkRectAllSectorNormalization_pos R hq
    simp [fkRectAllSectorNormalization, hzero] at hall
  field_simp


theorem balancedNormalization_negLog_eq_all_add_share
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectBalancedSectorNormalization R q) =
      -Real.log (fkRectAllSectorNormalization R q) +
        -Real.log (fkRectBalancedSectorShare R q) := by
  rw [fkRectBalancedSectorNormalization_eq_share_mul_all R hq,
    Real.log_mul
      (fkRectBalancedSectorShare_mem_Ioc R hq).1.ne'
      (fkRectAllSectorNormalization_pos R hq).ne']
  ring

end
end StatMech.FrontierD
