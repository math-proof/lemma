/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc37doubledhall.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc37_admDoubled_subset_boxDoubled (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc37_admDoubled n 𝒜 ℬ S ⊆ boxDoubled 𝒜 ℬ := by
  intro U hU
  rw [rc37_admDoubled, Finset.mem_image] at hU
  obtain ⟨R, hR, rfl⟩ := hU
  exact rc37_dblCompl_mem_boxDoubled 𝒜 ℬ
    (rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S hR)

open Classical in


theorem rc37_biUnion_admDoubled_card (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) :
    (𝒯.biUnion (rc37_admDoubled n 𝒜 ℬ)).card
      = (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  have hcomm : 𝒯.biUnion (rc37_admDoubled n 𝒜 ℬ)
      = (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).image (fun R => dbl R Rᶜ) := by
    rw [Finset.biUnion_image]; rfl
  rw [hcomm]
  refine Finset.card_image_of_injOn ?_
  intro R hR R' hR' h
  have := dbl_injective (a₁ := (R, Rᶜ)) (a₂ := (R', R'ᶜ)) h
  exact (Prod.mk.injEq _ _ _ _ ▸ this).1


end StatMech.Walls
