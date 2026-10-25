/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc67marriagesplit.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc68_Tin_subset_biUnion (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    rc67_Tin 𝒜 ℬ T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) :=
  rc67_Tin_subset_biUnion 𝒜 ℬ hbox

open Classical in


theorem rc68_biUnion_card_split (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    (T.biUnion (rc59_nbhd 𝒜 ℬ)).card
      = ((T.biUnion (rc59_nbhd 𝒜 ℬ)) \ rc67_Tin 𝒜 ℬ T).card + (rc67_Tin 𝒜 ℬ T).card :=
  (Finset.card_sdiff_add_card_eq_card (rc68_Tin_subset_biUnion 𝒜 ℬ hbox)).symm


end StatMech.Walls
