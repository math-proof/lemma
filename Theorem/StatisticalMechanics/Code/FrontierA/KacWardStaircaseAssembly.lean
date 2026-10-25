/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly


namespace StatMech.FrontierA

open scoped NNReal

open Set


@[simp] theorem kwEndpointParameter_zero (M : ℕ) (beta alpha : ℝ) :
    kwEndpointParameter M beta alpha 0 = 0 := by
  simp [kwEndpointParameter]

@[simp] theorem kwEndpointParameter_last (M : ℕ) (beta alpha : ℝ) :
    kwEndpointParameter M beta alpha (Fin.last (M + 2)) = 1 := by
  simp [kwEndpointParameter]

theorem kwEndpointParameter_strict
    (M : ℕ) (beta alpha : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (halpha : 0 < alpha)
    (hsum : alpha + beta < 1) (k : Fin (M + 2)) :
    kwEndpointParameter M beta alpha k.castSucc <
      kwEndpointParameter M beta alpha k.succ := by
  have hklt := k.isLt
  by_cases hk0 : k.val = 0
  · have hsucc0 : k.val + 1 ≠ 0 := by omega
    have hsuccLast : k.val + 1 ≠ M + 2 := by omega
    simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
      if_pos hk0, if_neg hsucc0, if_neg hsuccLast]
    norm_num [hk0]
    exact hbeta
  · by_cases hklast : k.val + 1 = M + 2
    · have hkLast : k.val ≠ M + 2 := by omega
      have hsub : k.val - 1 = M := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkLast, if_neg (by omega : k.val + 1 ≠ 0),
        if_pos hklast]
      rw [hsub]
      have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      rw [div_self hMreal, one_mul]
      linarith
    · have hkNotLast : k.val ≠ M + 2 := by omega
      have hsucc0 : k.val + 1 ≠ 0 := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkNotLast, if_neg hsucc0, if_neg hklast]
      have hkpos : 1 ≤ k.val := by omega
      have hsubSucc : k.val + 1 - 1 = k.val := by omega
      rw [hsubSucc]
      have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
      have hcentral : 0 < 1 - alpha - beta := by linarith
      have hnum : ((k.val - 1 : ℕ) : ℝ) < (k.val : ℝ) := by
        exact_mod_cast (by omega : k.val - 1 < k.val)
      have hfrac : ((k.val - 1 : ℕ) : ℝ) / M <
          (k.val : ℝ) / M :=
        (div_lt_div_iff_of_pos_right hMreal).mpr hnum
      simpa only [add_comm] using
        (add_lt_add_left (mul_lt_mul_of_pos_right hfrac hcentral) beta)

theorem kwEndpointParameter_step_le_inv
    (M : ℕ) (beta alpha : ℝ)
    (hM : 0 < M) (hbeta : 0 ≤ beta) (halpha : 0 ≤ alpha)
    (hbetaBound : beta ≤ (M : ℝ)⁻¹)
    (halphaBound : alpha ≤ (M : ℝ)⁻¹)
    (k : Fin (M + 2)) :
    kwEndpointParameter M beta alpha k.succ -
        kwEndpointParameter M beta alpha k.castSucc ≤ (M : ℝ)⁻¹ := by
  have hklt := k.isLt
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  by_cases hk0 : k.val = 0
  · have hsucc0 : k.val + 1 ≠ 0 := by omega
    have hsuccLast : k.val + 1 ≠ M + 2 := by omega
    simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
      if_pos hk0, if_neg hsucc0, if_neg hsuccLast]
    norm_num [hk0]
    exact hbetaBound
  · by_cases hklast : k.val + 1 = M + 2
    · have hkLast : k.val ≠ M + 2 := by omega
      have hsub : k.val - 1 = M := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkLast, if_neg (by omega : k.val + 1 ≠ 0),
        if_pos hklast]
      rw [hsub, div_self hMreal, one_mul]
      (convert halphaBound using 1; ring)
    · have hkNotLast : k.val ≠ M + 2 := by omega
      have hsucc0 : k.val + 1 ≠ 0 := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkNotLast, if_neg hsucc0, if_neg hklast]
      have hsubSucc : k.val + 1 - 1 = k.val := by omega
      rw [hsubSucc]
      have hstep : (((k.val : ℝ) / M) -
          (((k.val - 1 : ℕ) : ℝ) / M)) = (M : ℝ)⁻¹ := by
        have hkpos : 1 ≤ k.val := by omega
        have hcast : ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
          rw [Nat.cast_sub hkpos]
          norm_num
        rw [hcast]
        field_simp
        ring
      have hcentral : 1 - alpha - beta ≤ 1 := by linarith
      have hinv : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      calc
        beta + (k.val : ℝ) / M * (1 - alpha - beta) -
            (beta + ((k.val - 1 : ℕ) : ℝ) / M *
              (1 - alpha - beta)) =
            ((k.val : ℝ) / M - ((k.val - 1 : ℕ) : ℝ) / M) *
              (1 - alpha - beta) := by ring
        _ = (M : ℝ)⁻¹ * (1 - alpha - beta) := by rw [hstep]
        _ ≤ (M : ℝ)⁻¹ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hcentral hinv


end StatMech.FrontierA
