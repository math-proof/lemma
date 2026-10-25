/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectAllSectorNormalization_eq_residualExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectAllSectorNormalization R q =
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnEulerResidual R q omega := by
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hloop : fkRectOrientedLoopPartitionSum R lam =
      sixVertexTorusArrowPartitionSum R.medialTorus
        (fkQgt4SixVertexWeight q) := by
    rw [fkRectOrientedLoopPartitionSum_eq_sixVertex]
    exact congrArg (sixVertexTorusArrowPartitionSum R.medialTorus)
      (exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq)
  have hexpect := sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt
    R (by linarith : 0 < q) lam 0
  simp only [Nat.zero_le, if_true] at hexpect
  have hraw :
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectAllOrientedLoopTilt R q lam omega) =
        sixVertexTorusArrowPartitionSum R.medialTorus
            (fkQgt4SixVertexWeight q) /
          fkRectCriticalReducedZ R q := by
    rw [hexpect]
    exact congrArg (fun x => x / fkRectCriticalReducedZ R q) hloop
  have hres := sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area
    R hq 0
  simp only [Nat.zero_le, if_true] at hres
  have harea : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
    positivity
  unfold fkRectAllSectorNormalization
  rw [← hraw, hres]
  field_simp


theorem fkRectAllSectorNormalization_eq_zeroTurnNetExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectAllSectorNormalization R q =
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          ((2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
            q ^ fkRectNetIndicator R omega) := by
  rw [fkRectAllSectorNormalization_eq_residualExpectation R hq]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [fkRectZeroTurnEulerResidual_eq_netIndicator R hq]


theorem sixVertexTorusFixedCharge_zero_eq_balanced
    (T : EvenTorus) (c : Real) :
    sixVertexTorusFixedChargePartitionSum T 0 (Nat.zero_le _) c =
      svTorusBalancedArrowPartitionSum T c := by
  rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace,
    svTorusBalancedArrowPartitionSum_eq_sectorTrace]
  simp only [Nat.sub_zero]


theorem sixVertexTorusFixedCharge_zero_le_arrowPartitionSum
    (T : EvenTorus) {c : Real} (hc : 0 ≤ c) :
    sixVertexTorusFixedChargePartitionSum T 0 (Nat.zero_le _) c ≤
      sixVertexTorusArrowPartitionSum T c := by
  rw [sixVertexTorusFixedCharge_zero_eq_balanced]
  rw [← sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow]
  exact sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum
    T hc


theorem fkRectBalancedSectorNormalization_le_allSectorNormalization
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorNormalization R q ≤
      fkRectAllSectorNormalization R q := by
  unfold fkRectBalancedSectorNormalization fkRectAllSectorNormalization
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _
    (fkRectCriticalReducedZ_pos R (by linarith)).le
  exact sixVertexTorusFixedCharge_zero_le_arrowPartitionSum
    R.medialTorus (by
      linarith [two_lt_fkQgt4SixVertexWeight hq])

theorem fkRectAllSectorNormalization_pos
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    0 < fkRectAllSectorNormalization R q :=
  (fkRectBalancedSectorNormalization_pos R hq).trans_le
    (fkRectBalancedSectorNormalization_le_allSectorNormalization R hq)

theorem fkRectAllSectorNormalization_le_one
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectAllSectorNormalization R q ≤ 1 := by
  rw [fkRectAllSectorNormalization_eq_residualExpectation R hq]
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnEulerResidual R q omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_of_le_one_right
        (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega)
        (fkRectZeroTurnEulerResidual_le_one R hq omega)
    _ = 1 := sum_fkRectCriticalRandomClusterProb R (by linarith)


end
end StatMech.FrontierD
