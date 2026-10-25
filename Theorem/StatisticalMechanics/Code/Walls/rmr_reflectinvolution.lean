/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Def.StatisticalMechanics.Code.Walls.rmr_reflectinvolution
open Finset
open scoped StatMech


namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] theorem rmr_compl_apply (ω : ConfigSpace α) (a : α) : rmr_compl ω a = !ω a := rfl

omit [Fintype α] [DecidableEq α] in

theorem rmr_compl_eq_keyFlip_top (ω : ConfigSpace α) :
    rmr_compl ω = StatMech.poc_keyFlip (StatMech.poc_topKey : ConfigSpace α × ConfigSpace α) ω := by
  rw [StatMech.poc_keyFlip_top]; rfl

omit [Fintype α] [DecidableEq α] in


theorem rmr_compl_involutive :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) := by
  intro ω; funext a; simp [rmr_compl]

omit [Fintype α] [DecidableEq α] in

theorem rmr_compl_injective :
    Function.Injective (rmr_compl : ConfigSpace α → ConfigSpace α) :=
  rmr_compl_involutive.injective

omit [Fintype α] [DecidableEq α] in

theorem rmr_compl_bijective :
    Function.Bijective (rmr_compl : ConfigSpace α → ConfigSpace α) :=
  rmr_compl_involutive.bijective

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rmr_compl_compl (ω : ConfigSpace α) : rmr_compl (rmr_compl ω) = ω :=
  rmr_compl_involutive ω


open Classical in


theorem rmr_card_compl_mem (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) := by
  apply Finset.card_bij (fun ω _ => rmr_compl ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hω
  · intro a _ b _ h
    exact rmr_compl_injective h
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    refine ⟨rmr_compl ω, ?_, rmr_compl_involutive ω⟩
    rw [rmr_compl_involutive ω]; exact hω


end StatMech.Walls
