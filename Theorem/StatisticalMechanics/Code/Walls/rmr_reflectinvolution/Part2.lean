/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Def.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
open Finset
open scoped StatMech


namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] theorem rmr_mem_reflect (B : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ω ∈ rmr_reflect B ↔ rmr_compl ω ∈ B := Iff.rfl

omit [Fintype α] [DecidableEq α] in

theorem rmr_reflect_reflect (B : Set (ConfigSpace α)) : rmr_reflect (rmr_reflect B) = B := by
  ext ω; simp only [rmr_mem_reflect, rmr_compl_compl]

open Classical in


theorem rmr_card_reflect (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ rmr_reflect B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) := by
  simpa only [rmr_mem_reflect] using rmr_card_compl_mem B

open Classical in


theorem rmr_RHS_eq_inter (A B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  refine congrArg Finset.card (Finset.filter_congr (fun ω _ => ?_))
  simp only [Set.mem_inter_iff, rmr_mem_reflect]
  rfl


open Classical in


theorem rmr_reimerCardForm_iff_inter (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  unfold StatMech.poc_ReimerCardForm
  rw [rmr_RHS_eq_inter]

end StatMech.Walls
