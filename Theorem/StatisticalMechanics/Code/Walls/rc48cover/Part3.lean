/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc48cover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in


theorem rc48_complSubset_fires_fin3 :
    ∀ S ∈ rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁, Sᶜ ∈ rc48_C₁ := by
  rw [rc48_C₁, rc48_D₁]; decide

set_option maxRecDepth 4000 in


theorem rc48_boxSubReflInter_fails_C₁D₁_fin3 :
    ¬ (rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁ ⊆ rc20_reflInterComp 3 rc48_C₁ rc48_D₁) := by
  rw [rc48_C₁, rc48_D₁]; decide

set_option maxRecDepth 4000 in


theorem rc48_interCard_fails_C₁D₁_fin3 :
    (rc20_reflInterComp 3 rc48_C₁ rc48_D₁).card < #(rc48_C₁ ∩ rc48_D₁) := by
  rw [rc48_C₁, rc48_D₁]; decide

open Classical in


theorem rc48_wall_C₁D₁_via_complSubset :
    #(rc20_famCylBox rc48_C₁ rc48_D₁) ≤ #(rc10_reflInter rc48_C₁ rc48_D₁) := by
  refine rc48_famCylBox_le_reflInter_of_complSubset rc48_C₁ rc48_D₁ ?_
  intro S hS
  have h := rc48_complSubset_fires_fin3 S
  rw [rc20_famCylBoxComp_eq] at h
  exact h hS

set_option maxRecDepth 4000 in


theorem rc48_residual_c1_fails_fin3 :
    (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card < #(rc48_A₂ ∩ rc48_B₂) := by
  rw [rc48_A₂, rc48_B₂]; decide

set_option maxRecDepth 4000 in

theorem rc48_residual_c2_fails_fin3 :
    ¬ (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂ ⊆ rc20_reflInterComp 3 rc48_A₂ rc48_B₂) := by
  rw [rc48_A₂, rc48_B₂]; decide

set_option maxRecDepth 4000 in

theorem rc48_residual_c3_fails_fin3 :
    ¬ (∀ S ∈ rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂, Sᶜ ∈ rc48_A₂) := by
  rw [rc48_A₂, rc48_B₂]; decide

set_option maxRecDepth 4000 in


theorem rc48_wall_A₂B₂_holds :
    (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card := by
  rw [rc48_A₂, rc48_B₂]; decide


end StatMech.Walls
