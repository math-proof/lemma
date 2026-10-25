/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
import Def.StatisticalMechanics.Code.Walls.rc20reflection.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc20_cylBoxReflInter_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : rc18_CylBoxReflInter := by
  intro n A B
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact h n (eventFamily A) (eventFamily B)

open Classical in


theorem rc20_famCylBoxResidue_of_cylBoxReflInter (h : rc18_CylBoxReflInter) : rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  have hkey := h n (familyEvent 𝒜) (familyEvent ℬ)
  rw [rc20_cylBoxSupp_eq_famCylBox, rc10_eventFamily_familyEvent, rc10_eventFamily_familyEvent]
    at hkey
  exact hkey


theorem rc20_famCylBoxResidue_iff_cylBoxReflInter :
    rc20_FamCylBoxResidue ↔ rc18_CylBoxReflInter :=
  ⟨rc20_cylBoxReflInter_of_famCylBoxResidue, rc20_famCylBoxResidue_of_cylBoxReflInter⟩


open Classical in


theorem rc20_doubledReflection_right_univ (A : Set (ConfigSpace α)) :
    rc19_DoubledReflection A (Set.univ : Set (ConfigSpace α)) := by
  refine ⟨id, Set.injOn_id _, ?_⟩
  intro S hS
  rw [rc19_mem_reflInter_iff]
  refine ⟨?_, ?_⟩
  · exact (rc20_cylBoxSupp_self_mem hS).1
  · exact Set.mem_univ _

open Classical in


theorem rc20_doubledReflection_left_univ (B : Set (ConfigSpace α)) :
    rc19_DoubledReflection (Set.univ : Set (ConfigSpace α)) B := by
  refine ⟨fun S : Finset α => Sᶜ, ?_, ?_⟩
  · intro S _ S' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this
  · intro S hS
    rw [rc19_mem_reflInter_iff]
    refine ⟨Set.mem_univ _, ?_⟩
    rw [compl_compl]
    exact (rc20_cylBoxSupp_self_mem hS).2


end StatMech.Walls
