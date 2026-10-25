/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc66singletondet.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc67_self_mem_nbhd_of_box_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hbox : S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : S ∈ rc10_reflInter 𝒜 ℬ) :
    S ∈ rc59_nbhd 𝒜 ℬ S :=
  rc66_self_mem_nbhd 𝒜 ℬ hbox hRI

open Classical in


theorem rc67_Tin_self_subset_biUnion (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))}
    (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : ∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) :
    T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
  intro S hS
  have hself : S ∈ rc59_nbhd 𝒜 ℬ S :=
    rc67_self_mem_nbhd_of_box_reflInter 𝒜 ℬ (hbox S hS) (hRI S hS)
  exact Finset.mem_biUnion.mpr ⟨S, hS, hself⟩

open Classical in


theorem rc67_marriage_of_subset_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))}
    (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : ∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) :
    T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  Finset.card_le_card (rc67_Tin_self_subset_biUnion 𝒜 ℬ hbox hRI)


end StatMech.Walls
