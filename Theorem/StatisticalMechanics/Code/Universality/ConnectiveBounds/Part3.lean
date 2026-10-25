/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part3


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma zd_dropLast_isNB {d n : ℕ} {w : Fin (n + 1) → ZdStep d} (hw : ZdIsNB w) :
    ZdIsNB (zdDropLast w) := by
  intro i h
  have h' : ((i.castSucc : Fin (n + 1)) : ℕ) + 1 < n + 1 := by simp only [Fin.val_castSucc]; omega
  have key := hw i.castSucc h'
  show w (Fin.castSucc ⟨(i : ℕ) + 1, h⟩) ≠ zdReverse (w i.castSucc)
  have e1 : (Fin.castSucc (⟨(i : ℕ) + 1, h⟩ : Fin n))
      = (⟨((i.castSucc : Fin (n + 1)) : ℕ) + 1, h'⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  rw [e1]; exact key


lemma zd_fiber_card_le {d n : ℕ} (hn : 1 ≤ n) (v : Fin n → ZdStep d) :
    ({w ∈ zdNBWalks d (n + 1) | zdDropLast w = v}).card ≤ 2 * d - 1 := by
  set prev : ZdStep d := v ⟨n - 1, by omega⟩ with hprev
  rw [← zd_card_ne d (zdReverse prev)]
  apply Finset.card_le_card_of_injOn (fun w => w (Fin.last n))
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, zd_mem_nbWalks] at hw
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
      have hh : zdDropLast w ⟨n - 1, by omega⟩ = v ⟨n - 1, by omega⟩ := by rw [hdrop]
      simpa [zdDropLast, hprev] using hh
    rw [ev] at hnb2
    exact hnb2
  · intro w1 hw1 w2 hw2 hval
    simp only [Finset.coe_filter, Set.mem_setOf_eq, zd_mem_nbWalks] at hw1 hw2
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 := congrFun hw1.2 j
      have h2 := congrFun hw2.2 j
      simp only [zdDropLast] at h1 h2
      rw [h1, h2]
    · exact hval


lemma zd_nbCount_succ_le {d n : ℕ} (hn : 1 ≤ n) :
    zdNBCount d (n + 1) ≤ (2 * d - 1) * zdNBCount d n := by
  unfold zdNBCount
  have hmap : ∀ b ∈ (zdNBWalks d (n + 1)).image zdDropLast,
      ({w ∈ zdNBWalks d (n + 1) | zdDropLast w = b}).card ≤ 2 * d - 1 :=
    fun b _ => zd_fiber_card_le hn b
  have h1 := Finset.card_le_mul_card_image (zdNBWalks d (n + 1)) (2 * d - 1) hmap
  have himg : (zdNBWalks d (n + 1)).image zdDropLast ⊆ zdNBWalks d n := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact zd_mem_nbWalks.mpr (zd_dropLast_isNB (zd_mem_nbWalks.mp hw))
  calc (zdNBWalks d (n + 1)).card
        ≤ (2 * d - 1) * ((zdNBWalks d (n + 1)).image zdDropLast).card := h1
    _ ≤ (2 * d - 1) * (zdNBWalks d n).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)


lemma zd_nbCount_one (d : ℕ) : zdNBCount d 1 = 2 * d := by
  unfold zdNBCount zdNBWalks
  have : (Finset.univ.filter (fun w : Fin 1 → ZdStep d => ZdIsNB w)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro w _ i h
    exact absurd h (by omega)
  rw [this, Finset.card_univ, Fintype.card_fun, zd_card_step, Fintype.card_fin]
  ring


lemma zd_nbCount_bound (d n : ℕ) : zdNBCount d (n + 1) ≤ 2 * d * (2 * d - 1) ^ n := by
  induction n with
  | zero => simp [zd_nbCount_one]
  | succ k ih =>
    calc zdNBCount d (k + 1 + 1) ≤ (2 * d - 1) * zdNBCount d (k + 1) :=
            zd_nbCount_succ_le (by omega)
      _ ≤ (2 * d - 1) * (2 * d * (2 * d - 1) ^ k) := Nat.mul_le_mul_left _ ih
      _ = 2 * d * (2 * d - 1) ^ (k + 1) := by ring


theorem zd_sawCount_le {d n : ℕ} (hn : 1 ≤ n) :
    zdSAWCount d n ≤ 2 * d * (2 * d - 1) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  
  have hk : 0 + k + 1 - 1 = k := by omega
  rw [hk]
  calc zdSAWCount d (0 + k + 1) ≤ zdNBCount d (0 + k + 1) :=
        Finset.card_le_card zd_sawWalks_subset_nbWalks
    _ ≤ 2 * d * (2 * d - 1) ^ k := by
          have := zd_nbCount_bound d k
          simpa [Nat.zero_add] using this


end StatMech.Universality
