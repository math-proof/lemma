/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Lift the finset gap-insertion property to the submodule level via the frame-finset
correspondence, transporting the two distinct insertions along $S \mapsto \bigoplus_{i \in S} L_i$. -/
noncomputable def submoduleGapInsertionOfSubHyps
    (hcorr : FrameFinsetCorrespondenceHyp k n)
    (hgap_finset : FinsetChainGapHyp n) : SubmoduleGapInsertionHyp k n where
  find_gap := fun F chain hchain hcompat hproper hlen => by

    let extractF := hcorr.extract F
    let finset_chain : List (Finset (Fin n)) := chain.map extractF

    have hlen_fc : finset_chain.length = chain.length := List.length_map ..

    have hchain_fc : finset_chain.IsChain (· ⊂ ·) := by
      rw [List.isChain_iff_pairwise] at hchain ⊢
      rw [List.pairwise_map]
      exact hchain.imp_of_mem fun ha hb hab =>
        hcorr.extract_ssubset F _ _ (hcompat _ ha) (hcompat _ hb) hab


    have hne_fc : ∀ S ∈ finset_chain, S.Nonempty := by
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨V, hV, rfl⟩ := hS
      exact hcorr.extract_nonempty F V (hcompat V hV) (hproper V hV).1

    have hpr_fc : ∀ S ∈ finset_chain, S ≠ Finset.univ := by
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨V, hV, rfl⟩ := hS
      exact hcorr.extract_proper F V (hcompat V hV) (hproper V hV).2

    have hlen_fc' : finset_chain.length = n - 2 := by rw [hlen_fc, hlen]
    obtain ⟨T₁, T₂, pos, hne, hT₁_ne, hT₁_pr, hT₂_ne, hT₂_pr,
            hpos_fc, hbef₁, haft₁, hbef₂, haft₂⟩ :=
      hgap_finset.find_gap finset_chain hchain_fc hne_fc hpr_fc hlen_fc'

    let W₁ := ⨆ i ∈ T₁, F.lines i
    let W₂ := ⨆ i ∈ T₂, F.lines i
    refine ⟨W₁, W₂, pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

    · exact hcorr.lift_ne F T₁ T₂ hne

    · exact hcorr.lift_nonempty F T₁ hT₁_ne

    · exact hcorr.lift_proper F T₁ hT₁_pr

    · exact hcorr.lift_nonempty F T₂ hT₂_ne

    · exact hcorr.lift_proper F T₂ hT₂_pr

    · rwa [hlen_fc] at hpos_fc

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_take hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.take pos := by
        rw [← List.map_take]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : extractF V ⊂ T₁ := hbef₁ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F _ T₁ hS_V_lt

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_drop hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.drop pos := by
        rw [← List.map_drop]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : T₁ ⊂ extractF V := haft₁ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F T₁ _ hS_V_lt

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_take hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.take pos := by
        rw [← List.map_take]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : extractF V ⊂ T₂ := hbef₂ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F _ T₂ hS_V_lt

    · intro V hV
      have hV_chain : V ∈ chain := List.mem_of_mem_drop hV
      have hextract := hcorr.extract_eq F V (hcompat V hV_chain)
      have hS_V_mem : extractF V ∈ finset_chain.drop pos := by
        rw [← List.map_drop]
        exact List.mem_map_of_mem (f := extractF) hV
      have hS_V_lt : T₂ ⊂ extractF V := haft₂ _ hS_V_mem
      rw [hextract]
      exact hcorr.lift_ssubset F T₂ _ hS_V_lt

/-- Convert a submodule gap-insertion into a frame gap filler: the two distinct insertions
literally produce two distinct chambers via `insertIdx`. -/
noncomputable def frameGapFillerOfGapInsertion
    (hgap : SubmoduleGapInsertionHyp k n) : FrameGapFillerHyp k n where
  find_and_fill := fun F panel hcompat hlen => by
    obtain ⟨W₁, W₂, pos, hne, hW₁_bot, hW₁_top, hW₂_bot, hW₂_top,
            hpos, hbef₁, haft₁, hbef₂, haft₂⟩ :=
      hgap.find_gap F panel.chain panel.chain_strictly_increasing
        hcompat panel.chain_proper hlen
    refine ⟨W₁, W₂, pos, hne, hW₁_bot, hW₁_top, hW₂_bot, hW₂_top, hpos,
            ?_, ?_, ?_, ?_, ?_, ?_⟩

    · exact isChain_insertIdx_of_isChain panel.chain_strictly_increasing hpos hbef₁ haft₁

    · rw [List.length_insertIdx, if_pos hpos, hlen]
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega

    · exact isChain_insertIdx_of_isChain panel.chain_strictly_increasing hpos hbef₂ haft₂

    · rw [List.length_insertIdx, if_pos hpos, hlen]
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega

    · intro V hV
      rw [List.mem_insertIdx hpos] at hV
      cases hV with
      | inl h => subst h; exact ⟨hW₁_bot, hW₁_top⟩
      | inr h => exact panel.chain_proper V h

    · intro V hV
      rw [List.mem_insertIdx hpos] at hV
      cases hV with
      | inl h => subst h; exact ⟨hW₂_bot, hW₂_top⟩
      | inr h => exact panel.chain_proper V h


end GLnBuilding
