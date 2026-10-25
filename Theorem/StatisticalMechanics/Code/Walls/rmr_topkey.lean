/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech StatMech.ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in


theorem topFlip_eq_compl (ω : ConfigSpace α) :
    poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = fun a => !ω a :=
  poc_keyFlip_top ω

omit [Fintype α] [DecidableEq α] in


theorem topKey_slab_isWholeCube (ω : ConfigSpace α) :
    orbitKey (ω, poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω) = poc_topKey :=
  poc_orbitKey_top ω


open Classical in


theorem topKey_slabBox_eq_box (A B : Set (ConfigSpace α)) :
    poc_slabBox A B poc_topKey =
      Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B) :=
  poc_slabBox_top A B

open Classical in


theorem topKey_slabImg_eq_complImage (A B : Set (ConfigSpace α)) :
    poc_slabImg A B poc_topKey =
      Finset.univ.filter (fun ω => ω ∈ A ∧ (fun a => !ω a) ∈ B) :=
  poc_slabImg_top A B


end StatMech.Walls
