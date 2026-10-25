/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_cardformiffinter
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc2_slabBox_eq_slabFilter (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    poc_slabBox A B k =
      Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k) := by
  unfold poc_slabBox
  apply Finset.filter_congr
  intro ω _
  simp only [rc2_mem_slab]

open Classical in


theorem rc2_slabCard_iff_perKey (A B : Set (ConfigSpace α)) :
    poc_SlabCard A B ↔
      ∀ k : ConfigSpace α × ConfigSpace α,
        #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤
        #(Finset.univ.filter (fun ω => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)) := by
  unfold poc_SlabCard
  refine forall_congr' (fun k => ?_)
  rw [rc2_slabBox_eq_slabFilter, rc2_slabImg_eq_inter]


omit [Fintype α] [DecidableEq α] in


theorem rc2_orbitKey_symm (a b : ConfigSpace α) : orbitKey (a, b) = orbitKey (b, a) := by
  simp only [orbitKey]
  apply Prod.ext <;> funext c <;> simp [Bool.or_comm, Bool.and_comm]

omit [Fintype α] [DecidableEq α] in


theorem rc2_keyFlip_slab_invol (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    poc_keyFlip k (poc_keyFlip k ω) = ω :=
  rc2_keyFlip_involutive_on_slab k ω

omit [Fintype α] [DecidableEq α] in


theorem rc2_keyFlip_maps_slab (k : ConfigSpace α × ConfigSpace α) {ω : ConfigSpace α}
    (hω : ω ∈ rc2_slab k) : poc_keyFlip k ω ∈ rc2_slab k := by
  simp only [rc2_mem_slab] at hω ⊢
  rw [rc2_keyFlip_slab_invol, rc2_orbitKey_symm]
  exact hω


end StatMech.Walls
