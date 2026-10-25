/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc49doubled.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc49_reimer_closes_of_hallDoubled (h : rc49_HallDoubled) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc49_wall_of_hall 𝒜 ℬ (h n 𝒜 ℬ))


set_option maxRecDepth 4000 in


theorem rc49_jointImage_residual_maps_empty_to_zero :
    rc49_jointImage (∅ : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) ({0} : Finset (Fin 3))
      = ({0} : Finset (Fin 3)) := by
  rw [rc49_jointImage]; decide


theorem rc49_residual_KcylA :
    ∀ T : Finset (Fin 3), T ∩ ({1, 2} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∩ {1, 2} →
      T ∈ rc48_A₂ := by
  rw [rc48_A₂]; decide


theorem rc49_residual_LcylB :
    ∀ T : Finset (Fin 3), T ∩ ({0} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∩ {0} →
      T ∈ rc48_B₂ := by
  rw [rc48_B₂]; decide

open Classical in


theorem rc49_residual_target_mem_reflInter :
    ({0} : Finset (Fin 3)) ∈ rc10_reflInter rc48_A₂ rc48_B₂ := by
  have hd : Disjoint ({1, 2} : Finset (Fin 3)) ({0} : Finset (Fin 3)) := by decide
  have h := rc49_jointImage_mem_reflInter (𝒜 := rc48_A₂) (ℬ := rc48_B₂) (S := (∅ : Finset (Fin 3)))
    hd rc49_residual_KcylA rc49_residual_LcylB
  rwa [rc49_jointImage_residual_maps_empty_to_zero] at h

open Classical in


theorem rc49_residual_neighbourhood_nonempty :
    (rc49_neighbourhood rc48_A₂ rc48_B₂ (∅ : Finset (Fin 3))).Nonempty := by
  refine rc49_neighbourhood_nonempty (𝒜 := rc48_A₂) (ℬ := rc48_B₂) ?_
  rw [rc20_famCylBox, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, {1, 2}, {0}, by decide, rc49_residual_KcylA, rc49_residual_LcylB⟩

set_option maxRecDepth 4000 in


theorem rc49_wall_residual_holds :
    (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card := by
  rw [rc48_A₂, rc48_B₂]; decide


open Classical in


theorem rc49_reimer_joint_witness :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S K L : Finset (Fin 3)), Disjoint K L →
        (∀ T : Finset (Fin 3), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin 3), T ∩ L = S ∩ L → T ∈ ℬ) →
        rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S : Finset (Fin 3)),
          S ∈ rc20_famCylBox 𝒜 ℬ → (rc49_neighbourhood 𝒜 ℬ S).Nonempty)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc49_HallCond 𝒜 ℬ →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc49_HallDoubled → rc18_CylBoxReflInter)
      ∧ (rc49_jointImage (∅ : Finset (Fin 3)) ({1, 2}) ({0}) = ({0} : Finset (Fin 3)))
      ∧ (({0} : Finset (Fin 3)) ∈ rc10_reflInter rc48_A₂ rc48_B₂)
      ∧ ((rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card
          ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card) :=
  ⟨fun _ _ _ _ _ hKL hKA hLB => rc49_jointImage_mem_reflInter hKL hKA hLB,
    fun _ _ _ hS => rc49_neighbourhood_nonempty hS,
    fun 𝒜 ℬ h => rc49_wall_of_hall 𝒜 ℬ h,
    rc49_reimer_closes_of_hallDoubled,
    rc49_jointImage_residual_maps_empty_to_zero,
    rc49_residual_target_mem_reflInter,
    rc49_wall_residual_holds⟩

end StatMech.Walls
