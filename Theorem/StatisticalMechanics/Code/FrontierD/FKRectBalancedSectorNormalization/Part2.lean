/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBalancedNormalizationDefectDensity_eq_pressureDifference
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedNormalizationDefectDensity R q =
      fkRectCriticalReducedAreaDensity R q - Real.log (Real.sqrt q) -
        fkRectBalancedSectorAreaDensity R q := by
  have hs : Real.sqrt q ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith)).ne'
  have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R (by linarith)).ne'
  have hB : sixVertexTorusFixedChargePartitionSum R.medialTorus 0
      (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≠ 0 := by
    have h := sixVertexFixedCharge_div_fkZ_pos R hq 0 (Nat.zero_le _)
    exact fun hzero => by simp [hzero] at h
  have hA : (0 : Real) < (R.width * R.height : Nat) := by
    exact_mod_cast Nat.mul_pos R.width_pos R.height_pos
  unfold fkRectBalancedNormalizationDefectDensity
    fkRectCriticalReducedAreaDensity fkRectBalancedSectorAreaDensity
    fkRectBalancedSectorNormalization
  rw [Real.log_mul (pow_ne_zero _ hs) (div_ne_zero hB hZ),
    Real.log_pow, Real.log_div hB hZ]
  field_simp
  ring


theorem tendsto_fkRectBalancedNormalizationDefectDensity_zero_iff_pressure
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q) :
    Tendsto (fun n => fkRectBalancedNormalizationDefectDensity (R n) q)
        atTop (nhds 0) ↔
      Tendsto (fun n =>
        fkRectCriticalReducedAreaDensity (R n) q -
          Real.log (Real.sqrt q) -
          fkRectBalancedSectorAreaDensity (R n) q)
        atTop (nhds 0) := by
  apply tendsto_congr'
  filter_upwards [] with n
  exact fkRectBalancedNormalizationDefectDensity_eq_pressureDifference
    (R n) hq


theorem sixVertexFixedChargeRatio_mul_balancedNormalization_le_windingTail
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
          (fkQgt4SixVertexWeight q) /
        sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q)) *
        fkRectBalancedSectorNormalization R q ≤
      fkRectCriticalWindingTailMass R q r := by
  have h := sixVertexFixedCharge_div_chargeZero_le_windingTail_div_balanced
    R hq r hr
  rw [le_div_iff₀ (fkRectBalancedSectorNormalization_pos R hq)] at h
  exact h

theorem fkRectCriticalWindingTailMass_pos_of_fixedCharge
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    0 < fkRectCriticalWindingTailMass R q r := by
  have h := sixVertexFixedChargeRatio_mul_balancedNormalization_le_windingTail
    R hq r hr
  apply lt_of_lt_of_le _ h
  exact mul_pos
    (div_pos
      (by
        rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
        exact sixVertexSector_trace_pow_pos
          ((Nat.sub_le _ _).trans
            (Nat.div_le_self R.medialTorus.width 2))
          (by linarith [two_lt_fkQgt4SixVertexWeight hq])
          R.medialTorus.height)
      (by
        rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
        exact sixVertexSector_trace_pow_pos
          (Nat.div_le_self R.medialTorus.width 2)
          (by linarith [two_lt_fkQgt4SixVertexWeight hq])
          R.medialTorus.height))
    (fkRectBalancedSectorNormalization_pos R hq)


theorem fixedCharge_logRatio_add_logBalanced_le_logWindingTail
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    Real.log
        (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
            (fkQgt4SixVertexWeight q) /
          sixVertexTorusFixedChargePartitionSum R.medialTorus 0
            (Nat.zero_le _) (fkQgt4SixVertexWeight q)) +
      Real.log (fkRectBalancedSectorNormalization R q) ≤
        Real.log (fkRectCriticalWindingTailMass R q r) := by
  have hmul :=
    sixVertexFixedChargeRatio_mul_balancedNormalization_le_windingTail
      R hq r hr
  have hratio : 0 <
      sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
            (fkQgt4SixVertexWeight q) /
        sixVertexTorusFixedChargePartitionSum R.medialTorus 0
            (Nat.zero_le _) (fkQgt4SixVertexWeight q) := by
    apply div_pos
    · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
      exact sixVertexSector_trace_pow_pos
        ((Nat.sub_le _ _).trans
          (Nat.div_le_self R.medialTorus.width 2))
        (by linarith [two_lt_fkQgt4SixVertexWeight hq])
        R.medialTorus.height
    · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
      exact sixVertexSector_trace_pow_pos
        (Nat.div_le_self R.medialTorus.width 2)
        (by linarith [two_lt_fkQgt4SixVertexWeight hq])
        R.medialTorus.height
  have hlog := Real.log_le_log
    (mul_pos hratio (fkRectBalancedSectorNormalization_pos R hq)) hmul
  rw [Real.log_mul hratio.ne'
    (fkRectBalancedSectorNormalization_pos R hq).ne'] at hlog
  exact hlog


theorem windingTail_negLogRate_le_fixedCharge_add_normalizationDefect
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    -Real.log (fkRectCriticalWindingTailMass R q r) / R.height ≤
      -Real.log
          (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
              (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum R.medialTorus 0
              (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / R.height +
        -Real.log (fkRectBalancedSectorNormalization R q) / R.height := by
  have hlog := fixedCharge_logRatio_add_logBalanced_le_logWindingTail
    R hq r hr
  have hh : (0 : Real) < R.height := by exact_mod_cast R.height_pos
  rw [div_le_iff₀ hh]
  calc
    -Real.log (fkRectCriticalWindingTailMass R q r) ≤
        -Real.log
            (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
                (fkQgt4SixVertexWeight q) /
              sixVertexTorusFixedChargePartitionSum R.medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) +
          -Real.log (fkRectBalancedSectorNormalization R q) := by
      linarith
    _ = ((-Real.log
            (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr
                (fkQgt4SixVertexWeight q) /
              sixVertexTorusFixedChargePartitionSum R.medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / R.height) +
          (-Real.log (fkRectBalancedSectorNormalization R q) / R.height)) *
        R.height := by
      field_simp


theorem tendsto_balancedNormalization_negLog_div_height_zero_of_lower
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q)
    (lower : Nat → Real)
    (hlowerPos : ∀ n, 0 < lower n)
    (hlower : ∀ n,
      lower n ≤ fkRectBalancedSectorNormalization (R n) q)
    (hlowerCost : Tendsto (fun n =>
      -Real.log (lower n) / (R n).height) atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height)
    tendsto_const_nhds hlowerCost
  · filter_upwards [] with n
    exact div_nonneg
      (fkRectBalancedSectorNormalization_negLog_nonneg (R n) hq)
      (by positivity)
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hlog := Real.log_le_log (hlowerPos n) (hlower n)
    linarith


theorem tendsto_balancedNormalization_negLog_div_height_zero_of_uniformLower
    (R : Nat → FKRectTorus) {q a : Real} (hq : 4 < q)
    (ha : 0 < a)
    (hlower : ∀ n,
      a ≤ fkRectBalancedSectorNormalization (R n) q)
    (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop) :
    Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  apply tendsto_balancedNormalization_negLog_div_height_zero_of_lower
    R hq (fun _ => a) (fun _ => ha) hlower
  simpa using
    (tendsto_const_nhds.div_atTop hheight :
      Tendsto (fun n => -Real.log a / ((R n).height : Real))
        atTop (nhds 0))


theorem windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto
    (R : Nat → FKRectTorus)
    {q windingRate chargeRate normalizationRate : Real}
    (hq : 4 < q) (r : Nat)
    (hr : ∀ n, r ≤ (R n).medialTorus.width / 2)
    (hwind : Tendsto (fun n =>
      -Real.log (fkRectCriticalWindingTailMass (R n) q r) /
        (R n).height) atTop (nhds windingRate))
    (hcharge : Tendsto (fun n =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus r (hr n)
              (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
              (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height) atTop (nhds chargeRate))
    (hnormalization : Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds normalizationRate)) :
    windingRate ≤ chargeRate + normalizationRate := by
  apply le_of_tendsto_of_tendsto hwind (hcharge.add hnormalization)
  filter_upwards [] with n
  exact windingTail_negLogRate_le_fixedCharge_add_normalizationDefect
    (R n) hq r (hr n)


theorem windingTailRate_le_fixedChargeRate_of_tendsto
    (R : Nat → FKRectTorus) {q windingRate chargeRate : Real}
    (hq : 4 < q) (r : Nat)
    (hr : ∀ n, r ≤ (R n).medialTorus.width / 2)
    (hwind : Tendsto (fun n =>
      -Real.log (fkRectCriticalWindingTailMass (R n) q r) /
        (R n).height) atTop (nhds windingRate))
    (hcharge : Tendsto (fun n =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus r (hr n)
              (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
              (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height) atTop (nhds chargeRate))
    (hnormalization : Tendsto (fun n =>
      -Real.log (fkRectBalancedSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0)) :
    windingRate ≤ chargeRate := by
  simpa using
    (windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto
      R hq r hr hwind hcharge hnormalization)

end
end StatMech.FrontierD
