/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc49doubled.Part4
import Def.StatisticalMechanics.Code.Walls.rc50hall.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc50_reimer_closes_of_injectiveSelectionAll (h : rc50_InjectiveSelectionAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc50_wall_of_injectiveSelection (h n 𝒜 ℬ))

open Classical in


theorem rc50_injectiveSelectionAll_iff_hallDoubled :
    rc50_InjectiveSelectionAll ↔ rc49_HallDoubled := by
  constructor
  · intro h n 𝒜 ℬ; exact (rc50_hall_iff_injectiveSelection 𝒜 ℬ).mpr (h n 𝒜 ℬ)
  · intro h n 𝒜 ℬ; exact (rc50_hall_iff_injectiveSelection 𝒜 ℬ).mp (h n 𝒜 ℬ)


set_option maxRecDepth 4000 in


theorem rc50_box_residual_eq :
    rc20_famCylBox rc48_A₂ rc48_B₂ = {(∅ : Finset (Fin 3))} := by
  rw [← rc20_famCylBoxComp_eq, rc48_A₂, rc48_B₂]; decide

open Classical in


theorem rc50_injectiveSelection_residual :
    rc50_InjectiveSelection rc48_A₂ rc48_B₂ := by
  refine ⟨fun _ => ({1, 2}, {0}), ?_, ?_⟩
  · intro S hS
    rw [rc50_box_residual_eq, Finset.mem_singleton] at hS
    subst hS
    exact ⟨by decide, rc49_residual_KcylA, rc49_residual_LcylB⟩
  · intro S hS S' hS' _
    rw [Finset.mem_coe, rc50_box_residual_eq, Finset.mem_singleton] at hS hS'
    rw [hS, hS']

open Classical in


theorem rc50_hall_residual : rc49_HallCond rc48_A₂ rc48_B₂ :=
  rc50_hall_of_injectiveSelection rc50_injectiveSelection_residual


open Classical in


theorem rc50_reimer_involution_and_selection :
    (∀ (S K L : Finset (Fin 3)), Disjoint K L →
        rc49_jointImage (rc49_jointImage S K L) K L = S)
      ∧ (∀ (K L : Finset (Fin 3)), Disjoint K L →
          Function.Injective (fun S => rc49_jointImage S K L))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          rc49_HallCond 𝒜 ℬ ↔ rc50_InjectiveSelection 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          rc50_InjectiveSelection 𝒜 ℬ →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc50_InjectiveSelectionAll ↔ rc49_HallDoubled)
      ∧ (rc50_InjectiveSelectionAll → rc18_CylBoxReflInter)
      ∧ rc50_InjectiveSelection rc48_A₂ rc48_B₂
      ∧ rc49_HallCond rc48_A₂ rc48_B₂ :=
  ⟨fun S K L hKL => rc50_jointImage_involutive S K L hKL,
    fun K L hKL => rc50_jointImage_injective_of_fixed_witness K L hKL,
    fun 𝒜 ℬ => rc50_hall_iff_injectiveSelection 𝒜 ℬ,
    fun _ _ h => rc50_wall_of_injectiveSelection h,
    rc50_injectiveSelectionAll_iff_hallDoubled,
    rc50_reimer_closes_of_injectiveSelectionAll,
    rc50_injectiveSelection_residual,
    rc50_hall_residual⟩

end StatMech.Walls
