/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/FinsetGapCorrespondenceProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis.Part2
import Lemma.List.InsertIdx.eq.Take.of.Le_Length
import Mathlib.LinearAlgebra.Dimension.Finite


namespace GLnBuilding

section FinsetGap

variable {n : ℕ}

/-- The cardinality of any `Finset (Fin n)` is at most $n$. -/
theorem finset_card_le_n (S : Finset (Fin n)) : S.card ≤ n := by
  calc S.card ≤ Fintype.card (Fin n) := Finset.card_le_univ S
    _ = n := Fintype.card_fin n

/-- $|U \setminus L| = |U| - |L|$ when $L \subseteq U$. -/
theorem finset_card_sdiff_sub {lower upper : Finset (Fin n)} (hsub : lower ⊆ upper) :
    (upper \ lower).card = upper.card - lower.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

/-- In a strictly increasing chain of non-empty finsets, the $i$-th term has cardinality
at least $i+1$. -/
theorem chain_card_ge_succ {chain : List (Finset (Fin n))}
    (hpw : chain.Pairwise (· ⊂ ·))
    (hne : ∀ S ∈ chain, S.Nonempty)
    (i : ℕ) (hi : i < chain.length) :
    i + 1 ≤ (chain[i]).card := by
  induction i with
  | zero => exact Finset.card_pos.mpr (hne _ (List.getElem_mem hi))
  | succ k ih =>
    have hk : k < chain.length := by omega
    have := ih hk
    have := Finset.card_lt_card
      (List.pairwise_iff_getElem.mp hpw k (k + 1) hk hi (by omega))
    omega

/-- Core filler: if $|U \setminus L| \ge 2$, pick two distinct elements $a, b$ and form
$L \cup \{a\}$, $L \cup \{b\}$, giving two distinct intermediate proper non-empty finsets. -/
theorem gap_filler_core (lower upper : Finset (Fin n))
    (hsub : lower ⊆ upper) (hcard : 2 ≤ (upper \ lower).card) :
    ∃ T₁ T₂ : Finset (Fin n),
      T₁ ≠ T₂ ∧ T₁.Nonempty ∧ T₁ ≠ Finset.univ ∧
      T₂.Nonempty ∧ T₂ ≠ Finset.univ ∧
      lower ⊂ T₁ ∧ T₁ ⊂ upper ∧ lower ⊂ T₂ ∧ T₂ ⊂ upper := by
  have hpos1 : 0 < (upper \ lower).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos1
  have hpos2 : 0 < ((upper \ lower).erase a).card := by
    rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb_erase⟩ := Finset.card_pos.mp hpos2
  have hb := Finset.mem_of_mem_erase hb_erase
  have hab : a ≠ b := fun heq => by subst heq; simp at hb_erase
  rw [Finset.mem_sdiff] at ha hb
  refine ⟨insert a lower, insert b lower, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h; apply hab
    have hmem := (Finset.ext_iff.mp h a).mp (Finset.mem_insert_self a lower)
    simp [Finset.mem_insert] at hmem
    rcases hmem with rfl | haL
    · rfl
    · exact absurd haL ha.2
  · exact ⟨a, Finset.mem_insert_self a lower⟩
  · intro h; have hci := Finset.card_insert_of_notMem ha.2
    rw [h, Finset.card_univ, Fintype.card_fin] at hci
    have hcle := finset_card_le_n upper
    have hsd := finset_card_sdiff_sub hsub
    omega
  · exact ⟨b, Finset.mem_insert_self b lower⟩
  · intro h; have hci := Finset.card_insert_of_notMem hb.2
    rw [h, Finset.card_univ, Fintype.card_fin] at hci
    have hcle := finset_card_le_n upper
    have hsd := finset_card_sdiff_sub hsub
    omega
  · exact Finset.ssubset_insert ha.2
  ·
    constructor
    · intro x hx; simp [Finset.mem_insert] at hx
      rcases hx with rfl | hx; exact ha.1; exact hsub hx
    · intro h_eq
      have hsub' : upper \ lower ⊆ {a} := by
        intro x hx; rw [Finset.mem_sdiff] at hx; rw [Finset.mem_singleton]
        have hmem := h_eq hx.1; simp [Finset.mem_insert] at hmem
        rcases hmem with rfl | hxL; rfl; exact absurd hxL hx.2
      have := Finset.card_le_card hsub'; simp at this; omega
  · exact Finset.ssubset_insert hb.2
  · constructor
    · intro x hx; simp [Finset.mem_insert] at hx
      rcases hx with rfl | hx; exact hb.1; exact hsub hx
    · intro h_eq
      have hsub' : upper \ lower ⊆ {b} := by
        intro x hx; rw [Finset.mem_sdiff] at hx; rw [Finset.mem_singleton]
        have hmem := h_eq hx.1; simp [Finset.mem_insert] at hmem
        rcases hmem with rfl | hxL; rfl; exact absurd hxL hx.2
      have := Finset.card_le_card hsub'; simp at this; omega

/-- Earlier terms of a strictly-increasing chain are subsets of later terms. -/
theorem chain_elem_subset_of_lt {chain : List (Finset (Fin n))}
    (hpw : chain.Pairwise (· ⊂ ·))
    {bound j : ℕ} (hj : j < chain.length) (hbound : bound < chain.length)
    (hjb : j ≤ bound) :
    chain[j] ⊆ chain[bound] := by
  rcases eq_or_lt_of_le hjb with rfl | hlt
  · exact Finset.Subset.refl _
  · exact (List.pairwise_iff_getElem.mp hpw j bound hj hbound hlt).1

end FinsetGap
end GLnBuilding
