/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5


namespace StatMech.FrontierD

noncomputable section

theorem fkRectMedialLoopCount_dual
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectMedialLoopCount R (fkRectDualConfigurationEquiv R omega) =
      fkRectMedialLoopCount R omega := by
  unfold fkRectMedialLoopCount fkMedialLoopCount
  exact (Nat.card_congr
    (fkRectMedialDualShiftGraphIso R omega).connectedComponentEquiv).symm


theorem fkRectCriticalReducedWeight_eq_loop_net
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega =
      Real.sqrt q ^ (R.width * R.height : Nat) *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          q ^ fkRectNetIndicator R omega := by
  rw [fkRectCriticalReducedWeight_eq_loop_defect R hq,
    fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration]
  let s := fkRectNetIndicator R omega
  rw [show 2 * (s : Int) = (2 * s : Nat) by omega, zpow_natCast]
  change _ * _ * Real.sqrt q ^ (2 * s) = _ * _ * q ^ s
  have hpow : Real.sqrt q ^ (2 * s) = q ^ s := by
    calc
      Real.sqrt q ^ (2 * s) = (Real.sqrt q ^ 2) ^ s :=
        pow_mul (Real.sqrt q) 2 s
      _ = q ^ s := by rw [Real.sq_sqrt hq.le]
  rw [hpow]


theorem fkRectCriticalReducedWeight_dual_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectDualConfigurationEquiv R omega) ≤
      q * fkRectCriticalReducedWeight R q omega := by
  rw [fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectMedialLoopCount_dual]
  let B := Real.sqrt q ^ (R.width * R.height : Nat) *
    Real.sqrt q ^ fkRectMedialLoopCount R omega
  let s := fkRectNetIndicator R omega
  let t := fkRectNetIndicator R (fkRectDualConfigurationEquiv R omega)
  change B * q ^ t ≤ q * (B * q ^ s)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : s ≤ 1 := fkRectNetIndicator_le_one R omega
  have ht : t ≤ 1 := fkRectNetIndicator_le_one R
    (fkRectDualConfigurationEquiv R omega)
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hq2 : 1 ≤ q * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hq0 zero_le_one)]
  have hBq : 0 ≤ B * q := mul_nonneg hB hq0
  interval_cases s <;> interval_cases t <;> norm_num <;>
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hq),
      mul_nonneg hB (sub_nonneg.mpr hq2),
      mul_nonneg hBq (sub_nonneg.mpr hq)]


theorem fkRectCriticalReducedWeight_le_q_mul_dual
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega ≤
      q * fkRectCriticalReducedWeight R q
        (fkRectDualConfigurationEquiv R omega) := by
  rw [fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectMedialLoopCount_dual]
  let B := Real.sqrt q ^ (R.width * R.height : Nat) *
    Real.sqrt q ^ fkRectMedialLoopCount R omega
  let s := fkRectNetIndicator R omega
  let t := fkRectNetIndicator R (fkRectDualConfigurationEquiv R omega)
  change B * q ^ s ≤ q * (B * q ^ t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : s ≤ 1 := fkRectNetIndicator_le_one R omega
  have ht : t ≤ 1 := fkRectNetIndicator_le_one R
    (fkRectDualConfigurationEquiv R omega)
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hq2 : 1 ≤ q * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hq0 zero_le_one)]
  have hBq : 0 ≤ B * q := mul_nonneg hB hq0
  interval_cases s <;> interval_cases t <;> norm_num <;>
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hq),
      mul_nonneg hB (sub_nonneg.mpr hq2),
      mul_nonneg hBq (sub_nonneg.mpr hq)]


theorem fkRectCriticalRandomClusterProb_dual_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectDualConfigurationEquiv R omega) ≤
      q * fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [show q *
      (fkRectCriticalReducedWeight R q omega /
        fkRectCriticalReducedZ R q) =
      (q * fkRectCriticalReducedWeight R q omega) /
        fkRectCriticalReducedZ R q by ring]
  exact div_le_div_of_nonneg_right
    (fkRectCriticalReducedWeight_dual_le R hq omega)
    (fkRectCriticalReducedZ_pos R (zero_lt_one.trans_le hq)).le

theorem fkRectCriticalRandomClusterProb_le_q_mul_dual
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q omega ≤
      q * fkRectCriticalRandomClusterProb R q
        (fkRectDualConfigurationEquiv R omega) := by
  unfold fkRectCriticalRandomClusterProb
  rw [show q *
      (fkRectCriticalReducedWeight R q
          (fkRectDualConfigurationEquiv R omega) /
        fkRectCriticalReducedZ R q) =
      (q * fkRectCriticalReducedWeight R q
          (fkRectDualConfigurationEquiv R omega)) /
        fkRectCriticalReducedZ R q by ring]
  exact div_le_div_of_nonneg_right
    (fkRectCriticalReducedWeight_le_q_mul_dual R hq omega)
    (fkRectCriticalReducedZ_pos R (zero_lt_one.trans_le hq)).le


end
end StatMech.FrontierD
