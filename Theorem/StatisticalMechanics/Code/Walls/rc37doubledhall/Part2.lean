/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc37doubledhall.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc37_dblCompl_mem_boxDoubled (𝒜 ℬ : Finset (Finset α)) {R : Finset α}
    (hR : R ∈ rc10_reflInter 𝒜 ℬ) : dbl R Rᶜ ∈ boxDoubled 𝒜 ℬ := by
  rw [rc20_mem_reflInter] at hR
  rw [mem_boxDoubled]
  exact ⟨R, hR.1, Rᶜ, hR.2, disjoint_compl_right, rfl⟩


theorem rc37_dblCompl_injOn (s : Set (Finset α)) :
    Set.InjOn (fun R : Finset α => dbl R Rᶜ) s := by
  intro R _ R' _ h
  have := dbl_injective (a₁ := (R, Rᶜ)) (a₂ := (R', R'ᶜ)) h
  exact (Prod.mk.injEq _ _ _ _ ▸ this).1


theorem rc37_complBoxDoubled_subset (𝒜 ℬ : Finset (Finset α)) :
    rc37_complBoxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜 ℬ := by
  intro U hU
  rw [rc37_complBoxDoubled, Finset.mem_image] at hU
  obtain ⟨R, hR, rfl⟩ := hU
  exact rc37_dblCompl_mem_boxDoubled 𝒜 ℬ hR


theorem rc37_complBoxDoubled_card_eq_reflInter (𝒜 ℬ : Finset (Finset α)) :
    (rc37_complBoxDoubled 𝒜 ℬ).card = (rc10_reflInter 𝒜 ℬ).card := by
  rw [rc37_complBoxDoubled]
  exact Finset.card_image_of_injOn (rc37_dblCompl_injOn _)


end StatMech.Walls
