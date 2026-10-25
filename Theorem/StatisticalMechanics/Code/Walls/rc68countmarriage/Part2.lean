/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc67marriagesplit.Part3
import Def.StatisticalMechanics.Code.Walls.rc68countmarriage
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc68_marriage_of_countForm (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
    (hcount : rc68_CountForm 𝒜 ℬ T) :
    T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  rw [rc67_split_card 𝒜 ℬ T, rc68_biUnion_card_split 𝒜 ℬ hbox]
  rw [rc68_CountForm] at hcount
  omega

open Classical in


theorem rc68_countForm_of_marriage (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
    (hmar : T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) :
    rc68_CountForm 𝒜 ℬ T := by
  rw [rc68_CountForm]
  rw [rc67_split_card 𝒜 ℬ T, rc68_biUnion_card_split 𝒜 ℬ hbox] at hmar
  omega

open Classical in


theorem rc68_countForm_iff_marriage (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    rc68_CountForm 𝒜 ℬ T ↔ T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  ⟨rc68_marriage_of_countForm 𝒜 ℬ hbox, rc68_countForm_of_marriage 𝒜 ℬ hbox⟩


open Classical in

theorem rc68_witness_Tin :
    rc67_Tin rc66_wA rc66_wB {∅, {0}} = ({∅} : Finset (Finset (Fin 2))) := by
  rw [rc67_Tin, rc10_reflInter]; decide

open Classical in

theorem rc68_witness_Toff :
    rc67_Toff rc66_wA rc66_wB {∅, {0}} = ({{0}} : Finset (Finset (Fin 2))) := by
  rw [rc67_Toff, rc10_reflInter]; decide

open Classical in


theorem rc68_witness_biUnion :
    ({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)
      = ({∅, {1}} : Finset (Finset (Fin 2))) := by
  rw [Finset.biUnion_insert, Finset.singleton_biUnion, rc59_nbhd_eq_admOneSidedA,
    rc59_nbhd_eq_admOneSidedA]
  decide

open Classical in


theorem rc68_witness_countForm_holds :
    rc68_CountForm rc66_wA rc66_wB ({∅, {0}} : Finset (Finset (Fin 2))) := by
  rw [rc68_CountForm, rc68_witness_Toff, rc68_witness_biUnion, rc68_witness_Tin]
  decide

open Classical in


theorem rc68_witness_marriage_via_count :
    ({∅, {0}} : Finset (Finset (Fin 2))).card
      ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card := by
  refine rc68_marriage_of_countForm rc66_wA rc66_wB ?_ rc68_witness_countForm_holds
  intro S hS
  rw [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · exact rc66_witness_box.2.1
  · exact rc66_witness_box.1


end StatMech.Walls
