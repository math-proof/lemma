/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]

section Weighted

variable [Fintype α]


theorem wbutterfly_deficit_identity (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    fmarg w 𝒜 * fmarg w ℬ - wdpairs w 𝒜 ℬ
      = w i true * w i true
          * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i))
      + w i true * w i false
          * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.nonMemberSubfamily i)
              - wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i))
      + w i false * w i true
          * (fmarg' w i (𝒜.nonMemberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i)
              - wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i))
      + w i false * w i false
          * (fmarg' w i (𝒜.nonMemberSubfamily i) * fmarg' w i (ℬ.nonMemberSubfamily i)
              - wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  have hrec := wdpairs_fiber_recursion w 𝒜 ℬ i
  have hA := fmarg_split w 𝒜 i
  have hB := fmarg_split w ℬ i
  rw [hrec, hA, hB]
  ring


theorem wbutterfly_gap_ge_member {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
        + w i true * w i true
            * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i))
      ≤ fmarg w 𝒜 * fmarg w ℬ := by
  have hid := wbutterfly_deficit_identity w 𝒜 ℬ i
  have hMN := wdpairs'_le_mul hw i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
  have hNM := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)
  have hNN := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
  have h0 := hw i false
  have h1 := hw i true
  nlinarith [hid, mul_nonneg h1 h0, mul_nonneg h0 h1, mul_nonneg h0 h0,
    sub_nonneg.mpr hMN, sub_nonneg.mpr hNM, sub_nonneg.mpr hNN]


theorem fwt_symm_eq_const {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (S : Finset α) : fwt w S = ∏ x, w x true := by
  unfold fwt
  apply Finset.prod_congr rfl
  intro x _
  cases h : decide (x ∈ S) with
  | false => rw [hsym x]
  | true => rfl


theorem fmarg_symm_eq_const_mul_card {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 = (∏ x, w x true) * (𝒜.card : ℝ) := by
  unfold fmarg
  rw [Finset.sum_congr rfl (fun S _ => fwt_symm_eq_const hsym S)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]


theorem wdpairs_symm_eq_const_mul_count {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ = (∏ x, w x true) ^ 2 * (dpairsCount 𝒜 ℬ : ℝ) := by
  unfold wdpairs dpairsCount
  rw [Finset.sum_congr rfl (fun p _ => by
    rw [fwt_symm_eq_const hsym p.1, fwt_symm_eq_const hsym p.2])]
  rw [Finset.sum_const, nsmul_eq_mul, sq]
  ring


theorem wdpairs_symm_le_mul {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
  rw [wdpairs_symm_eq_const_mul_count hsym, fmarg_symm_eq_const_mul_card hsym,
    fmarg_symm_eq_const_mul_card hsym]
  have hc : (0 : ℝ) ≤ (∏ x, w x true) ^ 2 := sq_nonneg _
  have hcount : (dpairsCount 𝒜 ℬ : ℝ) ≤ (𝒜.card : ℝ) * (ℬ.card : ℝ) := by
    have := dpairsCount_le_mul 𝒜 ℬ
    calc (dpairsCount 𝒜 ℬ : ℝ) ≤ ((𝒜.card * ℬ.card : ℕ) : ℝ) := by exact_mod_cast this
      _ = (𝒜.card : ℝ) * (ℬ.card : ℝ) := by push_cast; ring
  calc (∏ x, w x true) ^ 2 * (dpairsCount 𝒜 ℬ : ℝ)
      ≤ (∏ x, w x true) ^ 2 * ((𝒜.card : ℝ) * (ℬ.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcount hc
    _ = (∏ x, w x true) * (𝒜.card : ℝ) * ((∏ x, w x true) * (ℬ.card : ℝ)) := by ring


end Weighted
end StatMech
