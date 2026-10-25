/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem intervalIntegral_offsetCorrectionTerm_mul_sin
    (lam : Real) (n : Nat) {m : Nat} (hm : 0 < m) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexOffsetCorrectionTerm lam n alpha *
        Real.sin ((m : Real) * alpha)) =
      if n + 1 = m then sixVertexGapCorrectionTerm lam n else 0 := by
  unfold sixVertexOffsetCorrectionTerm
  rw [show (fun alpha : Real =>
      (sixVertexGapCorrectionTerm lam n / Real.pi *
        Real.sin ((n + 1 : Real) * alpha)) *
          Real.sin ((m : Real) * alpha)) =
      fun alpha => (sixVertexGapCorrectionTerm lam n / Real.pi) *
        (Real.sin (((n + 1 : Nat) : Real) * alpha) *
          Real.sin ((m : Real) * alpha)) by
    funext alpha
    have hncast : (n + 1 : Real) = (((n + 1 : Nat) : Real)) := by
      norm_num
    rw [hncast]
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral_sin_nat_mul_mul_sin_nat_mul (by omega) hm]
  by_cases hnm : n + 1 = m
  · rw [if_pos hnm, if_pos hnm]
    field_simp [Real.pi_ne_zero]
  · rw [if_neg hnm, if_neg hnm, mul_zero]

theorem intervalIntegral_offsetCorrection_mul_sin
    {lam : Real} (hlam : 0 < lam) {m : Nat} (hm : 0 < m) :
    (∫ alpha in -Real.pi..Real.pi,
      (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
        Real.sin ((m : Real) * alpha)) =
      sixVertexGapCorrectionTerm lam (m - 1) := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left (2 / Real.pi)
  have hnorm : Summable (fun n : Nat =>
      ‖(offsetCorrectionMulSinContinuous lam n m).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajor
    rw [ContinuousMap.norm_le _ (by positivity :
      0 <= (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1))]
    intro alpha
    change |sixVertexOffsetCorrectionTerm lam n (alpha : Real) *
      Real.sin ((m : Real) * alpha)| <= _
    rw [abs_mul]
    calc
      |sixVertexOffsetCorrectionTerm lam n alpha| *
          |Real.sin ((m : Real) * alpha)| <=
        ‖sixVertexOffsetCorrectionTerm lam n alpha‖ * 1 := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul (le_rfl)
            (abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
            (abs_nonneg _) (abs_nonneg _)
      _ <= (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by
        simpa only [mul_one] using
          norm_sixVertexOffsetCorrectionTerm_le lam n alpha
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hseries :
      (∫ alpha in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha)) =
      ∑' n : Nat, ∫ alpha in -Real.pi..Real.pi,
        sixVertexOffsetCorrectionTerm lam n alpha *
          Real.sin ((m : Real) * alpha) := by
    calc
      _ = ∫ alpha in -Real.pi..Real.pi,
          (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha *
            Real.sin ((m : Real) * alpha)) := by
        apply intervalIntegral.integral_congr
        intro alpha _
        exact tsum_mul_right.symm
      _ = _ := by
        simpa only [offsetCorrectionMulSinContinuous] using hswap.symm
  rw [hseries]
  simp_rw [intervalIntegral_offsetCorrectionTerm_mul_sin lam _ hm]
  have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [tsum_eq_single (m - 1)]
  · rw [if_pos hpred]
  · intro n hn
    rw [if_neg]
    intro hnm
    apply hn
    omega


theorem sixVertexOffsetRapidityProfile_sineCoefficient
    {lam : Real} (hlam : 0 < lam) {m : Nat} (hm : 0 < m) :
    (1 / Real.pi) *
        (∫ alpha in -Real.pi..Real.pi,
          sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((m : Real) * alpha)) =
      (-1 : Real) ^ m * Real.tanh ((m : Real) * lam) /
        (Real.pi * (m : Real)) := by
  have hlinear := intervalIntegral_linearOffset_mul_sin hm
  have hcorr := intervalIntegral_offsetCorrection_mul_sin hlam hm
  have hcorrCont : Continuous (fun alpha =>
      ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) := by
    apply continuous_tsum
    · intro n
      unfold sixVertexOffsetCorrectionTerm
      fun_prop
    · have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
      have hq1 : Real.exp (-2 * lam) < 1 := by
        rw [<- Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      exact ((summable_geometric_of_lt_one hq0 hq1).comp_injective
        Nat.succ_injective).mul_left (2 / Real.pi)
    · intro n alpha
      exact norm_sixVertexOffsetCorrectionTerm_le lam n alpha
  have hsplit :
      (∫ alpha in -Real.pi..Real.pi,
        (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha) +
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha)) =
      (∫ alpha in -Real.pi..Real.pi,
        (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha)) +
      ∫ alpha in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha) := by
    exact intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun alpha : Real =>
        (-alpha / (2 * Real.pi)) *
          Real.sin ((m : Real) * alpha))).intervalIntegrable _ _)
      ((hcorrCont.mul (by fun_prop : Continuous (fun alpha : Real =>
        Real.sin ((m : Real) * alpha)))).intervalIntegrable _ _)
  unfold sixVertexOffsetRapidityProfile
  rw [show (fun alpha : Real =>
      (-alpha / (2 * Real.pi) +
        ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha)) =
      fun alpha =>
        (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha) +
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha) by
    funext alpha
    ring]
  rw [hsplit, hlinear, hcorr]
  rw [sixVertexGapCorrectionTerm]
  have hpredNat : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hpredReal : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
    exact_mod_cast hpredNat
  rw [hpredNat, hpredReal]
  field_simp [Real.pi_ne_zero, (by positivity : (m : Real) ≠ 0)]
  ring

end
end StatMech.FrontierD
