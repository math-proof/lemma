/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part4


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma zd_stepN_part1 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (i : ℕ) (hi : i < m) :
    zdStepN (zdPart1 (n := n) w) i = zdStepN w i := by
  unfold zdStepN zdPart1; rw [dif_pos hi, dif_pos (by omega)]

lemma zd_posN_part1 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (k : ℕ) (hk : k ≤ m) :
    zdPos (zdPart1 (n := n) w) k = zdPos w k := by
  unfold zdPos; apply Finset.sum_congr rfl; intro i hi
  exact zd_stepN_part1 w i (by have := Finset.mem_range.mp hi; omega)

lemma zd_stepN_part2 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (i : ℕ) :
    zdStepN (zdPart2 (m := m) w) i = zdStepN w (m + i) := by
  unfold zdStepN zdPart2
  by_cases hi : i < n
  · rw [dif_pos hi, dif_pos (by omega)]
  · rw [dif_neg hi, dif_neg (by omega)]

lemma zd_posN_part2 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (k : ℕ) :
    zdPos (zdPart2 (m := m) w) k = zdPos w (m + k) - zdPos w m := by
  unfold zdPos
  rw [eq_sub_iff_add_eq, add_comm, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  exact zd_stepN_part2 w i


lemma zd_part1_isSAW {d m n : ℕ} {w : Fin (m + n) → ZdStep d} (hw : ZdIsSAW w) :
    ZdIsSAW (zdPart1 (n := n) w) := by
  intro k1 k2 h1 h2 heq
  rw [zd_posN_part1 w k1 h1, zd_posN_part1 w k2 h2] at heq
  exact hw k1 k2 (by omega) (by omega) heq


lemma zd_part2_isSAW {d m n : ℕ} {w : Fin (m + n) → ZdStep d} (hw : ZdIsSAW w) :
    ZdIsSAW (zdPart2 (m := m) w) := by
  intro k1 k2 h1 h2 heq
  rw [zd_posN_part2 w k1, zd_posN_part2 w k2] at heq
  have hpe : zdPos w (m + k1) = zdPos w (m + k2) := sub_left_injective heq
  have := hw (m + k1) (m + k2) (by omega) (by omega) hpe
  omega


lemma zd_part_injective {d m n : ℕ} :
    Function.Injective
      (fun w : Fin (m + n) → ZdStep d => (zdPart1 (n := n) w, zdPart2 (m := m) w)) := by
  intro w1 w2 h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext i
  by_cases hi : (i : ℕ) < m
  · have := congrFun h1 ⟨i, hi⟩
    simpa [zdPart1] using this
  · have hi2 : (i : ℕ) - m < n := by omega
    have hc := congrFun h2 ⟨(i : ℕ) - m, hi2⟩
    simp only [zdPart2] at hc
    have e : (⟨m + ((i : ℕ) - m), by omega⟩ : Fin (m + n)) = i := by apply Fin.ext; simp; omega
    rw [e] at hc; exact hc


theorem zd_sawCount_submult (d m n : ℕ) :
    zdSAWCount d (m + n) ≤ zdSAWCount d m * zdSAWCount d n := by
  unfold zdSAWCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun w => (zdPart1 (n := n) w, zdPart2 (m := m) w))
  · intro w hw
    rw [Finset.mem_coe, zd_mem_sawWalks] at hw
    exact Finset.mem_coe.mpr (Finset.mk_mem_product
      (zd_mem_sawWalks.mpr (zd_part1_isSAW hw))
      (zd_mem_sawWalks.mpr (zd_part2_isSAW hw)))
  · intro w1 _ w2 _ h; exact zd_part_injective h


lemma zd_one_le_sawCount {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : 1 ≤ zdSAWCount d n := by
  calc 1 = d ^ 0 := by simp
    _ ≤ d ^ n := Nat.pow_le_pow_right hd (Nat.zero_le n)
    _ ≤ zdSAWCount d n := by
        calc d ^ n ≤ d ^ n := le_refl _
          _ ≤ _ := zd_pow_le_sawCount


end StatMech.Universality
