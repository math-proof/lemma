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
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBalancedSectorNormalization_pos
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    0 < fkRectBalancedSectorNormalization R q := by
  unfold fkRectBalancedSectorNormalization
  exact mul_pos (pow_pos (Real.sqrt_pos.2 (by linarith)) _)
    (sixVertexFixedCharge_div_fkZ_pos R hq 0 (Nat.zero_le _))

theorem fkRectBalancedSectorNormalization_eq_chargeZeroExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectBalancedSectorNormalization R q =
      Real.sqrt q ^ (R.width * R.height : Nat) *
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            fkRectFixedChargeTilt R q lam 0 (Nat.zero_le _) omega := by
  dsimp only
  unfold fkRectBalancedSectorNormalization
  rw [sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z
    R hq 0 (Nat.zero_le _)]


theorem sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q) =
      (Real.sqrt q ^ (R.width * R.height : Nat) *
          (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
              (fkQgt4SixVertexWeight q) /
            fkRectCriticalReducedZ R q)) /
        fkRectBalancedSectorNormalization R q := by
  unfold fkRectBalancedSectorNormalization
  have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R (by linarith)).ne'
  have hZ0 : sixVertexTorusFixedChargePartitionSum R.medialTorus 0
      (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≠ 0 := by
    have h := sixVertexFixedCharge_div_fkZ_pos R hq 0 (Nat.zero_le _)
    exact fun hz => by simp [hz] at h
  have hA : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 :=
    pow_ne_zero _ (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp [hZ, hZ0, hA]


theorem sixVertexFixedCharge_div_chargeZero_le_windingTail_div_balanced
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≤
      fkRectCriticalWindingTailMass R q r /
        fkRectBalancedSectorNormalization R q := by
  rw [sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio R hq r hr]
  apply div_le_div_of_nonneg_right _
    (fkRectBalancedSectorNormalization_pos R hq).le
  have hfinite := sixVertexFixedCharge_div_fkZ_le_windingTail_div_area
    R hq r hr
  have hA : 0 ≤ Real.sqrt q ^ (R.width * R.height : Nat) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfinite hA
  have hAne : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
    positivity
  field_simp [hAne] at hmul
  simpa only [mul_div_assoc] using hmul


theorem log_sqrtQ_le_fixedCharge_negLogRate_per_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    Real.log (Real.sqrt q) ≤
      -Real.log
          (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
              (fkQgt4SixVertexWeight q) /
            fkRectCriticalReducedZ R q) /
        (R.width * R.height : Nat) := by
  let x := sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
      (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q
  let A := R.width * R.height
  have hx : 0 < x := sixVertexFixedCharge_div_fkZ_pos R hq r hr
  have hxy : x ≤ (1 / Real.sqrt q) ^ A :=
    sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area R hq r hr
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hlog := Real.log_le_log hx hxy
  have hylog : Real.log ((1 / Real.sqrt q) ^ A) =
      -(A : Real) * Real.log (Real.sqrt q) := by
    rw [Real.log_pow, Real.log_div one_ne_zero hs, Real.log_one]
    ring
  rw [hylog] at hlog
  have hApos : (0 : Real) < A := by
    exact_mod_cast Nat.mul_pos R.width_pos R.height_pos
  rw [le_div_iff₀ hApos]
  dsimp [x, A] at hlog ⊢
  linarith

theorem sixVertexChargeOne_div_fkZ_le_residual_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          (if 1 ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectZeroTurnEulerResidual R q omega
          else 0)) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  exact sixVertexFixedCharge_div_fkZ_le_residual_div_area R hq 1
    (one_le_fkRectMedial_halfWidth R)

theorem sixVertexChargeOne_div_fkZ_le_windingTail_div_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      fkRectCriticalWindingTailMass R q 1 /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  exact sixVertexFixedCharge_div_fkZ_le_windingTail_div_area R hq 1
    (one_le_fkRectMedial_halfWidth R)

theorem sixVertexChargeOne_div_fkZ_le_invSqrtQ_pow_area
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
        fkRectCriticalReducedZ R q ≤
      (1 / Real.sqrt q) ^ (R.width * R.height : Nat) := by
  exact sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area R hq 1
    (one_le_fkRectMedial_halfWidth R)

end
end StatMech.FrontierD
