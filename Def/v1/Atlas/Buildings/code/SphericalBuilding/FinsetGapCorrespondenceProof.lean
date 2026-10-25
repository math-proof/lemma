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
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof


namespace GLnBuilding

section FinsetGap

variable {n : ℕ}

/-- Proof of `FinsetChainGapHyp`: any length-$(n-2)$ chain of proper non-empty subsets of
$\mathrm{Fin}\ n$ contains a position where two distinct insertions fit, by analysing
where cardinalities first deviate from the "tight" pattern $|S_i| = i+1$. -/
noncomputable def finsetChainGapHyp (n : ℕ) (hn2 : 2 ≤ n) : FinsetChainGapHyp n where
  find_gap := fun chain hchain hne hproper hlen => by
    rw [List.isChain_iff_pairwise] at hchain

    by_cases hn : n ≤ 2
    · have hn_eq : n = 2 := by omega
      subst hn_eq
      have hnil : chain.length = 0 := by omega
      have hchain_nil := List.eq_nil_of_length_eq_zero hnil; subst hchain_nil
      refine ⟨{(0 : Fin 2)}, {(1 : Fin 2)}, 0, ?_, Finset.singleton_nonempty _,
              ?_, Finset.singleton_nonempty _, ?_,
              le_refl _, fun S hS => absurd hS (List.not_mem_nil),
              fun S hS => absurd hS (List.not_mem_nil),
              fun S hS => absurd hS (List.not_mem_nil),
              fun S hS => absurd hS (List.not_mem_nil)⟩
      · intro h; have := Finset.ext_iff.mp h (0 : Fin 2); simp at this
      · intro h; have := Finset.ext_iff.mp h (1 : Fin 2); simp at this
      · intro h; have := Finset.ext_iff.mp h (0 : Fin 2); simp at this
    · push_neg at hn
      have hn3 : 3 ≤ n := hn
      have hlen_pos : 0 < chain.length := by omega

      by_cases hall : ∀ i, ∀ hi : i < chain.length, (chain[i]).card = i + 1
      ·
        have hlast : chain.length - 1 < chain.length := by omega
        have hlower_card : (chain[chain.length - 1]).card = n - 2 := by
          rw [hall (chain.length - 1) hlast, hlen]; omega
        have hdiff : 2 ≤ (Finset.univ \ chain[chain.length - 1]).card := by
          rw [finset_card_sdiff_sub (Finset.subset_univ _),
              Finset.card_univ, Fintype.card_fin, hlower_card]; omega
        obtain ⟨T₁, T₂, hne12, hne1, hpr1, hne2, hpr2, hlo1, hhi1, hlo2, hhi2⟩ :=
          gap_filler_core _ _ (Finset.subset_univ _) hdiff
        refine ⟨T₁, T₂, chain.length, hne12, hne1, hpr1, hne2, hpr2, le_refl _,
                ?_, ?_, ?_, ?_⟩
        · intro S hS; rw [List.take_length] at hS
          have hS_lower : S ⊆ chain[chain.length - 1] := by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            exact chain_elem_subset_of_lt hchain hj hlast (by omega)
          exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo1
        · intro S hS; rw [List.drop_length] at hS; exact absurd hS (List.not_mem_nil)
        · intro S hS; rw [List.take_length] at hS
          have hS_lower : S ⊆ chain[chain.length - 1] := by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            exact chain_elem_subset_of_lt hchain hj hlast (by omega)
          exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo2
        · intro S hS; rw [List.drop_length] at hS; exact absurd hS (List.not_mem_nil)
      ·
        push_neg at hall
        obtain ⟨i, hi, hmis⟩ := hall

        classical
        let P := fun k => ∃ hk : k < chain.length, (chain[k]'hk).card ≠ k + 1
        have hP : ∃ k, P k := ⟨i, hi, hmis⟩
        let pos := Nat.find hP
        have hpos_spec : P pos := Nat.find_spec hP
        obtain ⟨hpos_lt, hpos_mis⟩ := hpos_spec
        have hpos_card : pos + 2 ≤ (chain[pos]'hpos_lt).card := by
          have := chain_card_ge_succ hchain hne pos hpos_lt; omega
        have hprev : ∀ j, j < pos → (hj : j < chain.length) → (chain[j]'hj).card = j + 1 := by
          intro j hj hjlen
          by_contra h; exact Nat.find_min hP hj ⟨hjlen, h⟩
        by_cases hpos0 : pos = 0
        ·
          have hpos_lt0 : 0 < chain.length := by omega
          have helem_eq : chain[0]'hpos_lt0 = chain[pos]'hpos_lt := by
            congr 1; omega
          have hpos_card0 : 2 ≤ (chain[0]'hpos_lt0).card := by
            rw [helem_eq]; omega
          have hdiff : 2 ≤ (chain[0]'hpos_lt0 \ ∅).card := by simp; omega
          obtain ⟨T₁, T₂, hne12, hne1, hpr1, hne2, hpr2, hlo1, hhi1, hlo2, hhi2⟩ :=
            gap_filler_core ∅ (chain[0]'hpos_lt0) (Finset.empty_subset _) hdiff
          have hupper_proper := hproper _ (List.getElem_mem hpos_lt0)
          refine ⟨T₁, T₂, 0, hne12, hne1, ?_, hne2, ?_, (by omega : 0 ≤ chain.length),
                  fun S hS => absurd hS (by simp), ?_,
                  fun S hS => absurd hS (by simp), ?_⟩
          · intro h; rw [h] at hhi1
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi1.1 (Finset.mem_univ x))) hupper_proper
          · intro h; rw [h] at hhi2
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi2.1 (Finset.mem_univ x))) hupper_proper
          · intro S hS; rw [List.drop_zero] at hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            by_cases hj0 : j = 0
            · subst hj0; exact hhi1
            · exact Finset.ssubset_of_ssubset_of_subset hhi1
                (List.pairwise_iff_getElem.mp hchain 0 j (by omega) hj (by omega)).1
          · intro S hS; rw [List.drop_zero] at hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            by_cases hj0 : j = 0
            · subst hj0; exact hhi2
            · exact Finset.ssubset_of_ssubset_of_subset hhi2
                (List.pairwise_iff_getElem.mp hchain 0 j (by omega) hj (by omega)).1
        ·
          have hpos_pos : 0 < pos := Nat.pos_of_ne_zero hpos0
          have hprev_idx : pos - 1 < chain.length := by omega
          have hlower_card : (chain[pos - 1]'hprev_idx).card = pos := by
            rw [hprev (pos - 1) (by omega) hprev_idx]; omega
          have hlower_upper : chain[pos - 1]'hprev_idx ⊂ chain[pos]'hpos_lt :=
            List.pairwise_iff_getElem.mp hchain (pos - 1) pos hprev_idx hpos_lt (by omega)
          have hdiff : 2 ≤ (chain[pos]'hpos_lt \ chain[pos - 1]'hprev_idx).card := by
            rw [finset_card_sdiff_sub hlower_upper.1, hlower_card]; omega
          obtain ⟨T₁, T₂, hne12, hne1, hpr1, hne2, hpr2, hlo1, hhi1, hlo2, hhi2⟩ :=
            gap_filler_core _ _ hlower_upper.1 hdiff
          have hupper_proper := hproper _ (List.getElem_mem hpos_lt)
          refine ⟨T₁, T₂, pos, hne12, hne1, ?_, hne2, ?_, (by omega : pos ≤ chain.length),
                  ?_, ?_, ?_, ?_⟩
          · intro h; rw [h] at hhi1
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi1.1 (Finset.mem_univ x))) hupper_proper
          · intro h; rw [h] at hhi2
            exact absurd (Finset.eq_univ_iff_forall.mpr (fun x => hhi2.1 (Finset.mem_univ x))) hupper_proper
          · intro S hS
            have hS_lower : S ⊆ chain[pos - 1]'hprev_idx := by
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
              have hj_len : j < chain.length := by rw [List.length_take] at hj; omega
              have hj_pos : j ≤ pos - 1 := by rw [List.length_take] at hj; omega
              rw [← List.getElem_take' hj_len (by omega : j < pos)]
              exact chain_elem_subset_of_lt hchain hj_len hprev_idx hj_pos
            exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo1
          · intro S hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            rw [List.length_drop] at hj
            rw [List.getElem_drop]
            by_cases hjp : j = 0
            · subst hjp; simp; exact hhi1
            · exact Finset.ssubset_of_ssubset_of_subset hhi1
                (List.pairwise_iff_getElem.mp hchain pos (pos + j) hpos_lt (by omega) (by omega)).1
          · intro S hS
            have hS_lower : S ⊆ chain[pos - 1]'hprev_idx := by
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
              have hj_len : j < chain.length := by rw [List.length_take] at hj; omega
              have hj_pos : j ≤ pos - 1 := by rw [List.length_take] at hj; omega
              rw [← List.getElem_take' hj_len (by omega : j < pos)]
              exact chain_elem_subset_of_lt hchain hj_len hprev_idx hj_pos
            exact Finset.ssubset_of_subset_of_ssubset hS_lower hlo2
          · intro S hS
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
            rw [List.length_drop] at hj
            rw [List.getElem_drop]
            by_cases hjp : j = 0
            · subst hjp; simp; exact hhi2
            · exact Finset.ssubset_of_ssubset_of_subset hhi2
                (List.pairwise_iff_getElem.mp hchain pos (pos + j) hpos_lt (by omega) (by omega)).1

end FinsetGap


section FrameCorrespondence

variable (k : Type*) [Field k] (n : ℕ)

open Classical in
/-- Extract the index set $S \subseteq \mathrm{Fin}\ n$ such that $V = \bigoplus_{i \in S} F.\mathrm{lines}\ i$
(via classical choice), or `∅` if no such $S$ exists. -/
noncomputable def extractFinset (F : Frame k n) (V : Submodule k (Vec k n)) : Finset (Fin n) :=
  if h : F.IsCompatible k n V then Classical.choose h else ∅

end FrameCorrespondence
end GLnBuilding
