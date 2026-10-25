/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc48cover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc48_wall_of_cover (𝒜 ℬ : Finset (Finset α))
    (h : #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨
      rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨
      (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rcases h with h | h | h
  · exact rc47_famCylBox_le_reflInter_of_interCard 𝒜 ℬ h
  · exact rc47_famCylBox_le_reflInter_of_subset 𝒜 ℬ h
  · exact rc48_famCylBox_le_reflInter_of_complSubset 𝒜 ℬ h

open Classical in


theorem rc48_reimer_closes_of_coverAll (h : rc48_CoverAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc48_wall_of_cover 𝒜 ℬ (h n 𝒜 ℬ))


end StatMech.Walls
