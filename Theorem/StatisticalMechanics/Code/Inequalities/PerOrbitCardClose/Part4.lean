/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part4
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in

@[simp] theorem poc_keyFlip_top (ω : ConfigSpace α) :
    poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = fun a => !ω a := by
  funext a; simp only [poc_keyFlip, poc_flip, poc_topKey]; norm_num

omit [Fintype α] [DecidableEq α] in

@[simp] theorem poc_orbitKey_top (ω : ConfigSpace α) :
    orbitKey (ω, poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω) = poc_topKey := by
  rw [poc_keyFlip_top]
  simp only [orbitKey, poc_topKey]
  apply Prod.ext <;> funext a <;> cases ω a <;> simp

open Classical in

theorem poc_slabBox_top (A B : Set (ConfigSpace α)) :
    poc_slabBox A B (poc_topKey) =
      Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B) := by
  apply Finset.filter_congr
  intro ω _
  simp only [poc_orbitKey_top, and_true]

open Classical in

theorem poc_slabImg_top (A B : Set (ConfigSpace α)) :
    poc_slabImg A B (poc_topKey) =
      Finset.univ.filter (fun ω => ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
  apply Finset.filter_congr
  intro ω _
  rw [poc_orbitKey_top, poc_keyFlip_top]
  simp only [and_true]

end StatMech
