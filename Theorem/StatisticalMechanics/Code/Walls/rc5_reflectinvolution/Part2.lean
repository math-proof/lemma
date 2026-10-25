/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Def.StatisticalMechanics.Code.Walls.rc5_reflectinvolution
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc5_complEquiv_apply (ω : ConfigSpace α) : rc5_complEquiv ω = rmr_compl ω :=
  rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc5_complEquiv_symm_apply (ω : ConfigSpace α) :
    rc5_complEquiv.symm ω = rmr_compl ω := rfl

omit [Fintype α] [DecidableEq α] in


theorem rc5_complEquiv_symm : (rc5_complEquiv : ConfigSpace α ≃ ConfigSpace α).symm
    = rc5_complEquiv := rfl


open Classical in


theorem rc5_card_compl_mem (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) :=
  rmr_card_compl_mem B

open Classical in


theorem rc5_card_reflect (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ rmr_reflect B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) :=
  rmr_card_reflect B

open Classical in


theorem rc5_RHS_eq_inter (A B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) :=
  rmr_RHS_eq_inter A B


end StatMech.Walls
