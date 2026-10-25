/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc55nonproduct.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in

theorem rc56_box_res_card :
    (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card = 2 := by
  rw [rc56_Ares, rc56_Bres]; decide

set_option maxRecDepth 4000 in

theorem rc56_reflInter_res_card :
    (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card = 3 := by
  rw [rc56_Ares, rc56_Bres]; decide

set_option maxRecDepth 4000 in


theorem rc56_reflImageSet_res_card :
    (rc56_reflImageSet 3 rc56_Ares rc56_Bres).card = 1 := by
  rw [rc56_Ares, rc56_Bres]; decide

set_option maxRecDepth 4000 in


theorem rc56_symmDiff_collides_fin3 :
    (rc56_reflImageSet 3 rc56_Ares rc56_Bres).card
      < (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card := by
  rw [rc56_reflImageSet_res_card, rc56_box_res_card]; norm_num

set_option maxRecDepth 4000 in


theorem rc56_wall_holds_on_res :
    (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card
      ≤ (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card := by
  rw [rc56_box_res_card, rc56_reflInter_res_card]; norm_num


open Classical in


theorem rc56_reimer_closes_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue h

open Classical in

theorem rc56_reimerWprobCore_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : ReimerWprobCore :=
  rc55_reimerWprobCore_of_famCylBoxResidue h


open Classical in


theorem rc56_reimer_sandwich :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        rc20_famCylBox 𝒜 ℬ = (𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
            #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ))
      ∧ (rc56_WitnessedInterResidue ↔ rc20_FamCylBoxResidue)
      ∧ (rc56_WitnessedInterResidue → rc18_CylBoxReflInter)
      ∧ ((rc56_reflImageSet 3 rc56_Ares rc56_Bres).card
          < (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card)
      ∧ ((rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card
          ≤ (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card) :=
  ⟨fun 𝒜 ℬ => rc56_famCylBox_eq_inter_filter 𝒜 ℬ,
    fun 𝒜 ℬ => rc56_famCylBox_symm 𝒜 ℬ,
    fun 𝒜 ℬ => rc56_reflInter_card_symm 𝒜 ℬ,
    fun 𝒜 ℬ => rc56_wall_iff_witnessedInter 𝒜 ℬ,
    rc56_witnessedInterResidue_iff_famCylBoxResidue,
    rc56_reimer_closes_of_witnessedInterResidue,
    rc56_symmDiff_collides_fin3,
    rc56_wall_holds_on_res⟩

end StatMech.Walls
