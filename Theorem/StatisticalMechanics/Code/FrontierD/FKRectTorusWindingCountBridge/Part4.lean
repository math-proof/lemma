/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalWindingTailMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (r : Nat) :
    0 ≤ fkRectCriticalWindingTailMass R q r := by
  unfold fkRectCriticalWindingTailMass
  apply Finset.sum_nonneg
  intro omega homega
  split
  · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
  · exact le_rfl

theorem fkRectCriticalWindingTailMass_le_one
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (r : Nat) :
    fkRectCriticalWindingTailMass R q r ≤ 1 := by
  unfold fkRectCriticalWindingTailMass
  calc
    (∑ omega : R.Configuration,
      if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
        fkRectCriticalRandomClusterProb R q omega
      else 0) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      apply Finset.sum_le_sum
      intro omega homega
      split
      · exact le_rfl
      · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

theorem fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectAllOrientedLoopTilt R q lam omega =
      fkRectZeroTurnEulerResidual R q omega /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  rw [fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4 R hq]
  unfold fkRectZeroTurnEulerResidual
  ring


theorem sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (lam : Real) (r : Nat) :
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) =
      (∑ omega : R.Configuration,
        if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          ∑ arrows : SixVertexArrows R.medialTorus,
            fkRectOrientedLoopWeight R lam omega arrows
        else 0) / fkRectCriticalReducedZ R q := by
  calc
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) =
        ∑ omega : R.Configuration,
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            ∑ arrows : SixVertexArrows R.medialTorus,
              fkRectOrientedLoopWeight R lam omega arrows
          else 0) / fkRectCriticalReducedZ R q := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
      · rw [if_pos hU, if_pos hU]
        unfold fkRectCriticalRandomClusterProb fkRectAllOrientedLoopTilt
        have hw := (fkRectCriticalReducedWeight_pos R hq omega).ne'
        have hz := (fkRectCriticalReducedZ_pos R hq).ne'
        field_simp
      · simp [hU]
    _ = _ := by rw [Finset.sum_div]


theorem sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam r hr omega) ≤
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectAllOrientedLoopTilt R q lam omega
          else 0) := by
  dsimp only
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  let restricted : Real :=
    ∑ omega : R.Configuration,
      if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
        ∑ arrows : SixVertexArrows R.medialTorus,
          fkRectOrientedLoopWeight R lam omega arrows
      else 0
  have hraw : fkRectOrientedLoopSectorPartitionSum R
      (fkRectFixedChargeSector R r hr) lam ≤ restricted := by
    exact fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted
      R lam r hr
  have hsector : sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
        (fkQgt4SixVertexWeight q) =
      fkRectOrientedLoopSectorPartitionSum R
        (fkRectFixedChargeSector R r hr) lam := by
    rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
    rw [fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace]
    rw [exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq]
    simp [fkRectFixedChargeSector]
    rfl
  rw [sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq r hr]
  rw [sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt
    R (by linarith) lam r]
  rw [hsector]
  exact div_le_div_of_nonneg_right hraw
    (le_of_lt (fkRectCriticalReducedZ_pos R (by linarith)))


theorem sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (r : Nat) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectAllOrientedLoopTilt R q lam omega
        else 0)) =
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
  · rw [if_pos hU, if_pos hU,
      fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4 R hq]
    ring
  · simp [hU]

theorem sum_rcProb_mul_windingResidual_le_windingTailMass
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (r : Nat) :
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          fkRectZeroTurnEulerResidual R q omega
        else 0)) ≤
      fkRectCriticalWindingTailMass R q r := by
  unfold fkRectCriticalWindingTailMass
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
  · rw [if_pos hU, if_pos hU]
    exact mul_le_of_le_one_right
      (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega)
      (fkRectZeroTurnEulerResidual_le_one R hq omega)
  · simp [hU]


theorem sum_rcProb_mul_fixedChargeTilt_le_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectFixedChargeTilt R q lam r hr omega) ≤
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  calc
    _ ≤ ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectAllOrientedLoopTilt R q
              (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
              omega
          else 0) :=
      sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt
        R hq r hr
    _ = _ :=
      sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area
        R hq r

theorem sixVertexFixedCharge_div_fkZ_le_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  rw [← sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq r hr]
  exact sum_rcProb_mul_fixedChargeTilt_le_residual_div_area R hq r hr


theorem sixVertexFixedCharge_div_fkZ_le_windingTail_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      fkRectCriticalWindingTailMass R q r /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  calc
    _ ≤ (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) :=
      sixVertexFixedCharge_div_fkZ_le_residual_div_area R hq r hr
    _ ≤ _ := div_le_div_of_nonneg_right
      (sum_rcProb_mul_windingResidual_le_windingTailMass R hq r)
      (by positivity)


theorem sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (1 / Real.sqrt q) ^ (R.width * R.height : Nat) := by
  calc
    _ ≤ fkRectCriticalWindingTailMass R q r /
        Real.sqrt q ^ (R.width * R.height : Nat) :=
      sixVertexFixedCharge_div_fkZ_le_windingTail_div_area R hq r hr
    _ ≤ 1 / Real.sqrt q ^ (R.width * R.height : Nat) :=
      div_le_div_of_nonneg_right
        (fkRectCriticalWindingTailMass_le_one R (by linarith) r)
        (by positivity)
    _ = _ := by rw [one_div_pow]

theorem sixVertexFixedCharge_div_fkZ_pos
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    0 < sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q := by
  apply div_pos
  · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
    have hc : 0 < fkQgt4SixVertexWeight q := by
      linarith [two_lt_fkQgt4SixVertexWeight hq]
    exact sixVertexSector_trace_pow_pos
      (N := R.medialTorus.width)
      (n := R.medialTorus.width / 2 - r)
      (c := fkQgt4SixVertexWeight q)
      ((Nat.sub_le _ _).trans
        (Nat.div_le_self R.medialTorus.width 2))
      hc R.medialTorus.height
  · exact fkRectCriticalReducedZ_pos R (by linarith)


end
end StatMech.FrontierD
