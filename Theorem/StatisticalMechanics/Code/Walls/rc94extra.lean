/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc93extra.Part2
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc94_compl_involutive (w : ConfigSpace ι) : rc80_compl (rc80_compl w) = w := by
  funext i
  simp [rc80_compl]


theorem rc94_compl_injective : Function.Injective (rc80_compl : ConfigSpace ι → ConfigSpace ι) := by
  intro a b h
  have := congrArg rc80_compl h
  rwa [rc94_compl_involutive, rc94_compl_involutive] at this


theorem rc94_reflInterG_image_compl (A B : Finset (ConfigSpace ι)) :
    rc80_reflInterG A B = (rc80_reflInterG B A).image rc80_compl := by
  ext a
  simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨haA, hcaB⟩
    exact ⟨rc80_compl a, ⟨hcaB, by rw [rc94_compl_involutive]; exact haA⟩,
      rc94_compl_involutive a⟩
  · rintro ⟨b, ⟨hbB, hcbA⟩, rfl⟩
    exact ⟨hcbA, by rw [rc94_compl_involutive]; exact hbB⟩


theorem rc94_reflInterG_card_symm (A B : Finset (ConfigSpace ι)) :
    (rc80_reflInterG A B).card = (rc80_reflInterG B A).card := by
  rw [rc94_reflInterG_image_compl A B, Finset.card_image_of_injective _ rc94_compl_injective]


end StatMech.Walls
