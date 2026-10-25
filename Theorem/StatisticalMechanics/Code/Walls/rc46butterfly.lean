/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc45doubledcover.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc46butterfly
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc46_famCylBoxDoubled_card_eq (𝒜 ℬ : Finset (Finset α)) :
    (rc46_famCylBoxDoubled 𝒜 ℬ).card = (rc20_famCylBox 𝒜 ℬ).card := by
  rw [rc46_famCylBoxDoubled]
  exact Finset.card_image_of_injOn (rc37_dblCompl_injOn _)


set_option linter.unusedSectionVars false in


theorem rc46_doubleCompress_card_any (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (doubleCompress i 𝒜).card = 𝒜.card :=
  doubleCompress_card i 𝒜


theorem rc46_doubleCompress_famCylBoxDoubled_card (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (rc46_famCylBoxDoubled 𝒜 ℬ)).card = (rc46_famCylBoxDoubled 𝒜 ℬ).card :=
  doubleCompress_card i (rc46_famCylBoxDoubled 𝒜 ℬ)


theorem rc46_doubleCompress_complBoxDoubled_card (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (rc37_complBoxDoubled 𝒜 ℬ)).card = (rc37_complBoxDoubled 𝒜 ℬ).card :=
  doubleCompress_card i (rc37_complBoxDoubled 𝒜 ℬ)


end StatMech.Walls
