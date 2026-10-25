/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Green25_upper_solution.Part7
open Asymptotics Filter Finset


namespace Green25

lemma repeatPartition25_card_le {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) :
    #(repeatPartition25 q hB P).parts ≤ q * #P.parts := by
  simp only [repeatPartition25]
  rw [show q * #P.parts = ∑ _i : Fin q, #P.parts by simp]
  calc
    _ ≤ ∑ i : Fin q, #(shiftPartition25 (i.1 * B) P).parts :=
      Finset.card_biUnion_le
    _ = _ := by simp [shiftPartition25_card]

lemma restrictedSumset_shift25 (a : ℕ) (s : Finset ℕ) :
    (shift25 a s).restrictedSumset = shift25 (2 * a) s.restrictedSumset := by
  ext z
  simp only [Finset.restrictedSumset, Finset.mem_image, Finset.mem_offDiag, shift25,
    Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨u, hu, hux⟩, ⟨v, hv, hvy⟩, hxy⟩, rfl⟩
    subst x
    subst y
    refine ⟨u + v, ⟨u, v, ⟨hu, hv, ?_⟩, rfl⟩, ?_⟩
    · intro huv
      apply hxy
      omega
    · omega
  · rintro ⟨w, ⟨u, v, ⟨hu, hv, huv⟩, rfl⟩, rfl⟩
    refine ⟨a + u, a + v, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · exact ⟨v, hv, rfl⟩
    · intro h
      apply huv
      omega
    · omega

lemma repeatPartition25_sum_le {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) :
    #((repeatPartition25 q hB P).parts.biUnion Finset.restrictedSumset) ≤
      q * #(P.parts.biUnion Finset.restrictedSumset) := by
  let U := (Finset.univ : Finset (Fin q)).biUnion fun i =>
    shift25 (2 * (i.1 * B)) (P.parts.biUnion Finset.restrictedSumset)
  have hsub : (repeatPartition25 q hB P).parts.biUnion Finset.restrictedSumset ⊆ U := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    simp only [repeatPartition25, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
    obtain ⟨i, hp⟩ := hp
    change p ∈ P.parts.image (shift25 (i.1 * B)) at hp
    rw [Finset.mem_image] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    rw [restrictedSumset_shift25] at hzp
    dsimp [U]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [shift25, Finset.mem_image] at hzp ⊢
    obtain ⟨w, hw, rfl⟩ := hzp
    refine ⟨w, ?_, rfl⟩
    rw [Finset.mem_biUnion]
    exact ⟨p0, hp0, hw⟩
  calc
    _ ≤ #U := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin q, #(shift25 (2 * (i.1 * B))
        (P.parts.biUnion Finset.restrictedSumset)) := Finset.card_biUnion_le
    _ = q * #(P.parts.biUnion Finset.restrictedSumset) := by
      have hc : ∀ i : Fin q, #(shift25 (2 * (i.1 * B))
          (P.parts.biUnion Finset.restrictedSumset)) =
          #(P.parts.biUnion Finset.restrictedSumset) := by
        intro i
        exact Finset.card_image_iff.mpr fun _ _ _ _ h => Nat.add_left_cancel h
      simp_rw [hc]
      simp


lemma restrict_partition25 {s t : Finset ℕ} (P : Finpartition s) (ht : t ⊆ s) :
    ∃ Q : Finpartition t,
      #Q.parts ≤ #P.parts ∧
      Q.parts.biUnion Finset.restrictedSumset ⊆
        P.parts.biUnion Finset.restrictedSumset := by
  let raw := P.parts.image (fun p => p ∩ t)
  have hind : raw.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, raw, Finset.mem_image]
    rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hAB
    exact (P.disjoint hp hq (fun h => hAB (congrArg (fun u => u ∩ t) h))).mono
      (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hsup : raw.sup id = t := by
    apply Finset.ext
    intro x
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨u, hu, hxu⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_inter.mp hxu).2
    · intro hxt
      obtain ⟨p, hp, hxp⟩ := P.exists_mem (ht hxt)
      refine ⟨p ∩ t, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨hxp, hxt⟩
  let Q : Finpartition t := Finpartition.ofErase raw hind hsup
  refine ⟨Q, ?_, ?_⟩
  · calc
      #Q.parts ≤ #raw := Finset.card_erase_le
      _ ≤ #P.parts := Finset.card_image_le
  · intro z hz
    rw [Finset.mem_biUnion] at hz ⊢
    obtain ⟨u, huQ, hzu⟩ := hz
    change u ∈ (P.parts.image (fun p => p ∩ t)).erase ∅ at huQ
    have huRaw : u ∈ P.parts.image (fun p => p ∩ t) := (Finset.mem_erase.mp huQ).2
    obtain ⟨p, hp, hup⟩ := Finset.mem_image.mp huRaw
    subst u
    refine ⟨p, hp, ?_⟩
    rw [Finset.restrictedSumset] at hzu ⊢
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hzu
    refine Finset.mem_image.mpr ⟨xy, ?_, rfl⟩
    rw [Finset.mem_offDiag] at hxy ⊢
    exact ⟨(Finset.mem_inter.mp hxy.1).1,
      (Finset.mem_inter.mp hxy.2.1).1, hxy.2.2⟩


lemma tiled_digit_partition (t N : ℕ) (ht : 5 ≤ t)
    (hN : 2 ^ (4 * (2 ^ t) ^ 2) ≤ N) :
    ∃ P : Finpartition (Icc 1 N),
      #P.parts ≤ (N / (2 ^ (4 * (2 ^ t) ^ 2)) + 1) *
        candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) ∧
      10 * #(P.parts.biUnion Finset.restrictedSumset) < N := by
  let B := 2 ^ (4 * (2 ^ t) ^ 2)
  let q := N / B + 1
  have hB : 0 < B := by positivity
  obtain ⟨P₀, hPcard, hPsum⟩ := digit_partition t ht
  have hNB : N ≤ q * B := by
    calc
      N = N % B + B * (N / B) := (Nat.mod_add_div N B).symm
      _ = N % B + (N / B) * B := by ac_rfl
      _ ≤ B + (N / B) * B :=
        Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt N hB)) _
      _ = q * B := by simp [q]; ring
  have hsub : Icc 1 N ⊆ Icc 1 (q * B) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hNB⟩
  let R := repeatPartition25 q hB P₀
  obtain ⟨P, hPparts, hPsubset⟩ := restrict_partition25 R hsub
  refine ⟨P, ?_, ?_⟩
  · calc
      #P.parts ≤ #R.parts := hPparts
      _ ≤ q * #P₀.parts := repeatPartition25_card_le q hB P₀
      _ = q * candidate25 B := by
        simpa [B] using congrArg (q * ·) hPcard
      _ = (N / (2 ^ (4 * (2 ^ t) ^ 2)) + 1) *
          candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) := by rfl
  · have hsum : #(P.parts.biUnion Finset.restrictedSumset) ≤
        q * #(P₀.parts.biUnion Finset.restrictedSumset) := by
      exact (Finset.card_le_card hPsubset).trans
        (repeatPartition25_sum_le q hB P₀)
    have hq : 0 < q := by simp [q]
    have hqsmall : q * (20 * #(P₀.parts.biUnion Finset.restrictedSumset)) < q * B := by
      apply Nat.mul_lt_mul_of_pos_left
      · simpa [B] using hPsum
      · exact hq
    have hqB : q * B ≤ N + B := by
      simp only [q, Nat.add_mul]
      simpa using Nat.add_le_add_right (Nat.div_mul_le_self N B) B
    calc
      10 * #(P.parts.biUnion Finset.restrictedSumset) ≤
          10 * (q * #(P₀.parts.biUnion Finset.restrictedSumset)) :=
        Nat.mul_le_mul_left 10 hsum
      _ < N := by
        have hBN : B ≤ N := by simpa [B] using hN
        nlinarith


end Green25
