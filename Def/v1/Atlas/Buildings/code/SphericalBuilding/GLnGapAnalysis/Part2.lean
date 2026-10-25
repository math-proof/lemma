/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis.Part2


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Wrap a `FrameGapFillerHyp` into a `PanelGapHyp` by reading off the two distinct extended
chambers obtained from the insertions $W_1 \ne W_2$. -/
noncomputable def panelGapOfFrameGapFiller
    (filler : FrameGapFillerHyp k n) : PanelGapHyp k n where
  fill_gap := fun F panel hcompat hlen => by
    obtain ⟨W₁, W₂, pos, hne, hW₁_bot, hW₁_top, hW₂_bot, hW₂_top,
            hpos, hch₁, hlen₁, hch₂, hlen₂, hpr₁, hpr₂⟩ :=
      filler.find_and_fill F panel hcompat hlen
    refine ⟨panel.chain.insertIdx pos W₁, panel.chain.insertIdx pos W₂,
            ?_, hch₁, hpr₁, hlen₁, ?_, hch₂, hpr₂, hlen₂, ?_, ?_, ?_⟩
    · intro h; simp [h] at hlen₁
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega
    · intro h; simp [h] at hlen₂
      have : 0 < panel.chain.length := List.length_pos_of_ne_nil panel.chain_nonempty
      omega
    · intro V hV; rw [List.mem_insertIdx hpos]; exact Or.inr hV
    · intro V hV; rw [List.mem_insertIdx hpos]; exact Or.inr hV
    · exact insertIdx_ne_of_ne hne hpos


/-- Convert a `PanelGapHyp` into a `DirectPanelExtensionHyp` by packaging the two chains
as `SubspaceFlag`s with the chamber property. -/
noncomputable def directPanelExtensionOfGap
    (gap : PanelGapHyp k n) : DirectPanelExtensionHyp k n where
  extend := fun F panel hcompat hlen => by
    obtain ⟨ch₁, ch₂, hne₁, hch₁, hpr₁, hlen₁,
            hne₂, hch₂, hpr₂, hlen₂, hmem₁, hmem₂, hdist⟩ :=
      gap.fill_gap F panel hcompat hlen
    let C₁ : SubspaceFlag k n :=
      { chain := ch₁
        chain_nonempty := hne₁
        chain_strictly_increasing := hch₁
        chain_proper := hpr₁ }
    let C₂ : SubspaceFlag k n :=
      { chain := ch₂
        chain_nonempty := hne₂
        chain_strictly_increasing := hch₂
        chain_proper := hpr₂ }
    have hchamber₁ : IsChamber k n C₁ := hlen₁
    have hchamber₂ : IsChamber k n C₂ := hlen₂
    have hne : C₁ ≠ C₂ := by
      intro heq; apply hdist; exact congrArg SubspaceFlag.chain heq
    exact ⟨C₁, C₂, hchamber₁, hchamber₂, hne, hmem₁, hmem₂⟩

end GLnBuilding
