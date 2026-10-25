/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.TriLattice.Part4


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma tri_dropLast_isNB {n : ℕ} {w : Fin (n + 1) → TriStep} (hw : TriIsNB w) :
    TriIsNB (triDropLast w) := by
  intro i h
  have h' : ((i.castSucc : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
    simp only [Fin.val_castSucc]; omega
  have key := hw i.castSucc h'
  show w (Fin.castSucc ⟨(i : ℕ) + 1, h⟩) ≠ triReverse (w i.castSucc)
  have e1 : (Fin.castSucc (⟨(i : ℕ) + 1, h⟩ : Fin n))
      = (⟨((i.castSucc : Fin (n + 1)) : ℕ) + 1, h'⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  rw [e1]; exact key


lemma tri_fiber_card_le {n : ℕ} (hn : 1 ≤ n) (v : Fin n → TriStep) :
    ({w ∈ triNBWalks (n + 1) | triDropLast w = v}).card ≤ 5 := by
  set prev : TriStep := v ⟨n - 1, by omega⟩ with hprev
  rw [← tri_card_ne (triReverse prev)]
  apply Finset.card_le_card_of_injOn (fun w => w (Fin.last n))
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, tri_mem_nbWalks] at hw
    obtain ⟨hnb, hdrop⟩ := hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    have hidx : ((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 < n + 1 := by omega
    have hnb2 := hnb ⟨n - 1, by omega⟩ hidx
    have eL : (⟨((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1, hidx⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext; simp; omega
    rw [eL] at hnb2
    have e2 : (⟨n - 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext; simp
    rw [e2] at hnb2
    have ev : w (Fin.castSucc ⟨n - 1, by omega⟩) = prev := by
      have hh : triDropLast w ⟨n - 1, by omega⟩ = v ⟨n - 1, by omega⟩ := by rw [hdrop]
      simpa [triDropLast, hprev] using hh
    rw [ev] at hnb2
    exact hnb2
  · intro w1 hw1 w2 hw2 hval
    simp only [Finset.coe_filter, Set.mem_setOf_eq, tri_mem_nbWalks] at hw1 hw2
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 := congrFun hw1.2 j
      have h2 := congrFun hw2.2 j
      simp only [triDropLast] at h1 h2
      rw [h1, h2]
    · exact hval


lemma tri_nbCount_succ_le {n : ℕ} (hn : 1 ≤ n) :
    triNBCount (n + 1) ≤ 5 * triNBCount n := by
  unfold triNBCount
  have hmap : ∀ b ∈ (triNBWalks (n + 1)).image triDropLast,
      ({w ∈ triNBWalks (n + 1) | triDropLast w = b}).card ≤ 5 :=
    fun b _ => tri_fiber_card_le hn b
  have h1 := Finset.card_le_mul_card_image (triNBWalks (n + 1)) 5 hmap
  have himg : (triNBWalks (n + 1)).image triDropLast ⊆ triNBWalks n := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact tri_mem_nbWalks.mpr (tri_dropLast_isNB (tri_mem_nbWalks.mp hw))
  calc (triNBWalks (n + 1)).card
        ≤ 5 * ((triNBWalks (n + 1)).image triDropLast).card := h1
    _ ≤ 5 * (triNBWalks n).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)


lemma tri_nbCount_one : triNBCount 1 = 6 := by
  unfold triNBCount triNBWalks
  have : (Finset.univ.filter (fun w : Fin 1 → TriStep => TriIsNB w)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro w _ i h
    exact absurd h (by omega)
  rw [this, Finset.card_univ, Fintype.card_fun, tri_card_step, Fintype.card_fin]
  norm_num


lemma tri_nbCount_bound (n : ℕ) : triNBCount (n + 1) ≤ 6 * 5 ^ n := by
  induction n with
  | zero => simp [tri_nbCount_one]
  | succ k ih =>
    calc triNBCount (k + 1 + 1) ≤ 5 * triNBCount (k + 1) :=
            tri_nbCount_succ_le (by omega)
      _ ≤ 5 * (6 * 5 ^ k) := Nat.mul_le_mul_left _ ih
      _ = 6 * 5 ^ (k + 1) := by ring


theorem tri_sawCount_le {n : ℕ} (hn : 1 ≤ n) :
    triSAWCount n ≤ 6 * 5 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have hk : 0 + k + 1 - 1 = k := by omega
  rw [hk]
  calc triSAWCount (0 + k + 1) ≤ triNBCount (0 + k + 1) :=
        Finset.card_le_card tri_sawWalks_subset_nbWalks
    _ ≤ 6 * 5 ^ k := by
          have := tri_nbCount_bound k
          simpa [Nat.zero_add] using this


end StatMech.Universality
