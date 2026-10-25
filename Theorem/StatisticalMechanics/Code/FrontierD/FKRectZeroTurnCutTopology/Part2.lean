/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectMedialHorizontalSeamComponents
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    C ∈ fkRectMedialHorizontalSeamComponents R omega ↔
      FKRectMedialHitsHorizontalSeam R omega C := by
  classical
  simp [fkRectMedialHorizontalSeamComponents]


theorem fkRectMedialHorizontalSeamComponents_card_le_two_width
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkRectMedialHorizontalSeamComponents R omega).card ≤
      2 * R.width := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let componentAt : Fin R.medialTorus.width →
      FKMedialLoop R.medialTorus pairing := fun i =>
    (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
      (fkMedialVerticalSeamDart R.medialTorus i)
  have hsub : fkRectMedialHorizontalSeamComponents R omega ⊆
      (Finset.univ : Finset (Fin R.medialTorus.width)).image componentAt := by
    intro C hC
    rw [Finset.mem_image]
    rw [mem_fkRectMedialHorizontalSeamComponents] at hC
    rcases hC with ⟨i, hi⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact hi
  calc
    (fkRectMedialHorizontalSeamComponents R omega).card ≤
        ((Finset.univ : Finset (Fin R.medialTorus.width)).image
          componentAt).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin R.medialTorus.width)).card :=
      Finset.card_image_le
    _ = 2 * R.width := by
      rw [Finset.card_univ, Fintype.card_fin]
      rfl


end
end StatMech.FrontierD
