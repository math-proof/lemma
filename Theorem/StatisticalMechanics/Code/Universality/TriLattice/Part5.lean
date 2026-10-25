/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.TriLattice.Part5


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma tri_stepN_part1 {m n : ℕ} (w : Fin (m + n) → TriStep) (i : ℕ) (hi : i < m) :
    triStepN (triPart1 (n := n) w) i = triStepN w i := by
  unfold triStepN triPart1; rw [dif_pos hi, dif_pos (by omega)]

lemma tri_posN_part1 {m n : ℕ} (w : Fin (m + n) → TriStep) (k : ℕ) (hk : k ≤ m) :
    triPos (triPart1 (n := n) w) k = triPos w k := by
  unfold triPos; apply Finset.sum_congr rfl; intro i hi
  exact tri_stepN_part1 w i (by have := Finset.mem_range.mp hi; omega)

lemma tri_stepN_part2 {m n : ℕ} (w : Fin (m + n) → TriStep) (i : ℕ) :
    triStepN (triPart2 (m := m) w) i = triStepN w (m + i) := by
  unfold triStepN triPart2
  by_cases hi : i < n
  · rw [dif_pos hi, dif_pos (by omega)]
  · rw [dif_neg hi, dif_neg (by omega)]

lemma tri_posN_part2 {m n : ℕ} (w : Fin (m + n) → TriStep) (k : ℕ) :
    triPos (triPart2 (m := m) w) k = triPos w (m + k) - triPos w m := by
  unfold triPos
  rw [eq_sub_iff_add_eq, add_comm, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  exact tri_stepN_part2 w i


lemma tri_part1_isSAW {m n : ℕ} {w : Fin (m + n) → TriStep} (hw : TriIsSAW w) :
    TriIsSAW (triPart1 (n := n) w) := by
  intro k1 k2 h1 h2 heq
  rw [tri_posN_part1 w k1 h1, tri_posN_part1 w k2 h2] at heq
  exact hw k1 k2 (by omega) (by omega) heq


lemma tri_part2_isSAW {m n : ℕ} {w : Fin (m + n) → TriStep} (hw : TriIsSAW w) :
    TriIsSAW (triPart2 (m := m) w) := by
  intro k1 k2 h1 h2 heq
  rw [tri_posN_part2 w k1, tri_posN_part2 w k2] at heq
  have hpe : triPos w (m + k1) = triPos w (m + k2) := sub_left_injective heq
  have := hw (m + k1) (m + k2) (by omega) (by omega) hpe
  omega


lemma tri_part_injective {m n : ℕ} :
    Function.Injective
      (fun w : Fin (m + n) → TriStep => (triPart1 (n := n) w, triPart2 (m := m) w)) := by
  intro w1 w2 h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext i
  by_cases hi : (i : ℕ) < m
  · have := congrFun h1 ⟨i, hi⟩
    simpa [triPart1] using this
  · have hi2 : (i : ℕ) - m < n := by omega
    have hc := congrFun h2 ⟨(i : ℕ) - m, hi2⟩
    simp only [triPart2] at hc
    have e : (⟨m + ((i : ℕ) - m), by omega⟩ : Fin (m + n)) = i := by apply Fin.ext; simp; omega
    rw [e] at hc; exact hc


theorem tri_sawCount_submult (m n : ℕ) :
    triSAWCount (m + n) ≤ triSAWCount m * triSAWCount n := by
  unfold triSAWCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun w => (triPart1 (n := n) w, triPart2 (m := m) w))
  · intro w hw
    rw [Finset.mem_coe, tri_mem_sawWalks] at hw
    exact Finset.mem_coe.mpr (Finset.mk_mem_product
      (tri_mem_sawWalks.mpr (tri_part1_isSAW hw))
      (tri_mem_sawWalks.mpr (tri_part2_isSAW hw)))
  · intro w1 _ w2 _ h; exact tri_part_injective h


lemma tri_one_le_sawCount (n : ℕ) : 1 ≤ triSAWCount n := by
  calc 1 = 3 ^ 0 := by simp
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le n)
    _ ≤ triSAWCount n := tri_pow_le_sawCount


end StatMech.Universality
