/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc66singletondet.Part2
import Def.StatisticalMechanics.Code.Walls.rc67marriagesplit
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc67_split_card (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) :
    T.card = (rc67_Tin 𝒜 ℬ T).card + (rc67_Toff 𝒜 ℬ T).card := by
  rw [rc67_Tin, rc67_Toff, Finset.card_inter_add_card_sdiff]

open Classical in


theorem rc67_Tin_subset_biUnion (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    rc67_Tin 𝒜 ℬ T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
  intro S hS
  rw [rc67_Tin, Finset.mem_inter] at hS
  obtain ⟨hST, hSRI⟩ := hS
  have hself : S ∈ rc59_nbhd 𝒜 ℬ S :=
    rc67_self_mem_nbhd_of_box_reflInter 𝒜 ℬ (hbox S hST) hSRI
  exact Finset.mem_biUnion.mpr ⟨S, hST, hself⟩

end StatMech.Walls
