/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6localmirror.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.rc6localmirror.Part2
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc6_mirrorL_apply (L : Set α) (ω : ConfigSpace α) (a : α) :
    rc6_mirrorL L ω a = if a ∈ L then !ω a else ω a := rfl

open Classical in


theorem rc6_mirrorL_eq_localMirror_diag (L : Set α) (ω : ConfigSpace α) (a : α) :
    rc6_mirrorL L ω a = rc6_localMirror L a ω a := by
  rw [rc6_mirrorL_apply, rc6_localMirror_apply]
  by_cases h : a ∈ L
  · rw [if_pos h, if_pos ⟨rfl, h⟩]
  · rw [if_neg h, if_neg (by rintro ⟨_, hh⟩; exact h hh)]

open Classical in

theorem rc6_mirrorL_involutive (L : Set α) : Function.Involutive (rc6_mirrorL L) := by
  intro ω; funext a
  rw [rc6_mirrorL_apply, rc6_mirrorL_apply]
  by_cases h : a ∈ L
  · rw [if_pos h, if_pos h, Bool.not_not]
  · rw [if_neg h, if_neg h]

open Classical in

theorem rc6_mirrorL_injective (L : Set α) : Function.Injective (rc6_mirrorL L) :=
  (rc6_mirrorL_involutive L).injective

open Classical in


theorem rc6_mirrorL_agreeOn_of_disjoint {K L : Set α} (ω : ConfigSpace α) (hKL : Disjoint K L) :
    agreeOn K ω (rc6_mirrorL L ω) := by
  intro a haK
  rw [rc6_mirrorL_apply, if_neg (Set.disjoint_left.mp hKL haK)]

open Classical in


theorem rc6_compl_mirrorL_agreeOn_L (L : Set α) (ω : ConfigSpace α) :
    agreeOn L ω (rmr_compl (rc6_mirrorL L ω)) := by
  intro a haL
  rw [rmr_compl_apply, rc6_mirrorL_apply, if_pos haL, Bool.not_not]

open Classical in


theorem rc6_mirrorL_mem {A B : Set (ConfigSpace α)} {K L : Set α} {ω : ConfigSpace α}
    (hKL : Disjoint K L) (hA : OccursOn A K ω) (hB : OccursOn B L ω) :
    rc6_mirrorL L ω ∈ A ∩ rmr_reflect B := by
  refine ⟨hA _ (rc6_mirrorL_agreeOn_of_disjoint ω hKL), ?_⟩
  rw [rmr_mem_reflect]
  exact hB _ (rc6_compl_mirrorL_agreeOn_L L ω)


open Classical in


theorem rc6_boxReflectInjection_of_uniformWitness {A B : Set (ConfigSpace α)} {K L : Set α}
    (hKL : Disjoint K L)
    (hA : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn A K ω)
    (hB : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn B L ω) :
    rc5_BoxReflectInjection A B := by
  refine ⟨rc6_mirrorL L, ?_, ?_⟩
  · intro ω _ ω' _ h
    exact (rc6_mirrorL_involutive L).injective h
  · intro ω hω
    exact rc6_mirrorL_mem hKL (hA ω hω) (hB ω hω)

open Classical in


theorem rc6_boxReflectInjection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc5_BoxReflectInjection A B := by
  apply rc6_boxReflectInjection_of_uniformWitness (K := (↑S : Set α)) (L := (↑T : Set α))
    (Finset.disjoint_coe.mpr hST)
  · intro ω hω
    exact (hA.occursOn_iff ω).mpr (disjointOccurrence_subset_inter A B hω).1
  · intro ω hω
    exact (hB.occursOn_iff ω).mpr (disjointOccurrence_subset_inter A B hω).2

end StatMech.Walls
