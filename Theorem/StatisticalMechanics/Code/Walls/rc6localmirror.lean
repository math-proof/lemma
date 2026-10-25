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
import Def.StatisticalMechanics.Code.Walls.rc6localmirror
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc6_localMirror_apply (L : Set α) (i : α) (ω : ConfigSpace α) (a : α) :
    rc6_localMirror L i ω a = if a = i ∧ i ∈ L then !ω a else ω a := rfl


open Classical in


theorem rc6_localMirror_at_mem (L : Set α) (i : α) (ω : ConfigSpace α) (hi : i ∈ L) :
    rc6_localMirror L i ω i = !ω i := by
  rw [rc6_localMirror_apply, if_pos ⟨rfl, hi⟩]

open Classical in


theorem rc6_localMirror_at_not_mem (L : Set α) (i : α) (ω : ConfigSpace α) (hi : i ∉ L) :
    rc6_localMirror L i ω i = ω i := by
  rw [rc6_localMirror_apply, if_neg (by rintro ⟨_, h⟩; exact hi h)]

open Classical in


theorem rc6_localMirror_off (L : Set α) (i : α) (ω : ConfigSpace α) {a : α} (ha : a ≠ i) :
    rc6_localMirror L i ω a = ω a := by
  rw [rc6_localMirror_apply, if_neg (by rintro ⟨h, _⟩; exact ha h)]


open Classical in


theorem rc6_localMirror_localMirror (L : Set α) (i : α) (ω : ConfigSpace α) :
    rc6_localMirror L i (rc6_localMirror L i ω) = ω := by
  funext a
  rw [rc6_localMirror_apply]
  by_cases h : a = i ∧ i ∈ L
  · rw [if_pos h, rc6_localMirror_apply, if_pos h, Bool.not_not]
  · rw [if_neg h, rc6_localMirror_apply, if_neg h]

open Classical in

theorem rc6_localMirror_involutive (L : Set α) (i : α) :
    Function.Involutive (rc6_localMirror L i) :=
  rc6_localMirror_localMirror L i

open Classical in


theorem rc6_localMirror_involutive_at (L : Set α) (i : α) (ω : ConfigSpace α) :
    rc6_localMirror L i (rc6_localMirror L i ω) i = ω i := by
  rw [rc6_localMirror_localMirror]

open Classical in

theorem rc6_localMirror_injective (L : Set α) (i : α) :
    Function.Injective (rc6_localMirror L i) :=
  (rc6_localMirror_involutive L i).injective


open Classical in


theorem rc6_localMirror_agreeOn_of_disjoint {K L : Set α} (i : α) (ω : ConfigSpace α)
    (hKL : Disjoint K L) : agreeOn K ω (rc6_localMirror L i ω) := by
  intro a haK
  rw [rc6_localMirror_apply]
  by_cases h : a = i ∧ i ∈ L
  · obtain ⟨rfl, hiL⟩ := h
    exact absurd haK (Set.disjoint_left.mp hKL · hiL)
  · rw [if_neg h]

open Classical in


theorem rc6_localMirror_mem_A {A : Set (ConfigSpace α)} {K L : Set α} (i : α) {ω : ConfigSpace α}
    (hKL : Disjoint K L) (hA : OccursOn A K ω) : rc6_localMirror L i ω ∈ A :=
  hA _ (rc6_localMirror_agreeOn_of_disjoint i ω hKL)


open Classical in


theorem rc6_localMirror_eq_compl_at {L : Set α} (i : α) (ω : ConfigSpace α) (hi : i ∈ L) :
    rc6_localMirror L i ω i = rmr_compl ω i := by
  rw [rc6_localMirror_at_mem L i ω hi, rmr_compl_apply]


open Classical in


theorem rc6_localMirror_node {A : Set (ConfigSpace α)} {K L : Set α} (i : α) {ω : ConfigSpace α}
    (hKL : Disjoint K L) (hA : OccursOn A K ω) :
    (∀ a, a ≠ i → rc6_localMirror L i ω a = ω a)
      ∧ (i ∈ L → rc6_localMirror L i ω i = !ω i)
      ∧ (i ∉ L → rc6_localMirror L i ω i = ω i)
      ∧ rc6_localMirror L i (rc6_localMirror L i ω) i = ω i
      ∧ rc6_localMirror L i ω ∈ A
      ∧ (i ∈ L → rc6_localMirror L i ω i = rmr_compl ω i) :=
  ⟨fun _ ha => rc6_localMirror_off L i ω ha,
   fun hi => rc6_localMirror_at_mem L i ω hi,
   fun hi => rc6_localMirror_at_not_mem L i ω hi,
   rc6_localMirror_involutive_at L i ω,
   rc6_localMirror_mem_A i hKL hA,
   fun hi => rc6_localMirror_eq_compl_at i ω hi⟩


end StatMech.Walls
