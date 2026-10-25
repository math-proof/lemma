/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc48cover.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in


theorem rc48_famCylBox_not_compressionInvariant :
    (rc20_famCylBoxComp 3 (rc48_downCompress 3 0 rc48_A₂)
        (rc48_downCompress 3 0 rc48_E₂)).card
      ≠ (rc20_famCylBoxComp 3 rc48_A₂ rc48_E₂).card := by
  rw [rc48_A₂, rc48_E₂, rc48_downCompress, rc48_downCompress]; decide


open Classical in


theorem rc48_reimer_threeway_cover :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) →
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨
            rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨
            (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc48_CoverAll → rc18_CylBoxReflInter)
      ∧ (#(rc20_famCylBox rc48_C₁ rc48_D₁) ≤ #(rc10_reflInter rc48_C₁ rc48_D₁))
      ∧ (¬ (rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁ ⊆ rc20_reflInterComp 3 rc48_C₁ rc48_D₁))
      ∧ ((rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card < #(rc48_A₂ ∩ rc48_B₂))
      ∧ ((rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card)
      ∧ ((rc20_famCylBoxComp 3 (rc48_downCompress 3 0 rc48_A₂)
            (rc48_downCompress 3 0 rc48_E₂)).card
          ≠ (rc20_famCylBoxComp 3 rc48_A₂ rc48_E₂).card) :=
  ⟨fun 𝒜 ℬ h => rc48_famCylBox_le_reflInter_of_complSubset 𝒜 ℬ h,
    fun 𝒜 ℬ h => rc48_wall_of_cover 𝒜 ℬ h,
    rc48_reimer_closes_of_coverAll,
    rc48_wall_C₁D₁_via_complSubset,
    rc48_boxSubReflInter_fails_C₁D₁_fin3,
    rc48_residual_c1_fails_fin3,
    rc48_wall_A₂B₂_holds,
    rc48_famCylBox_not_compressionInvariant⟩

end StatMech.Walls
