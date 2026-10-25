/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc59doubledcover.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc59_wall_of_indepHall_pair (𝒜 ℬ : Finset (Finset (Fin n)))
    (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  refine rc33_wall_of_hallOneSidedA n 𝒜 ℬ ?_
  intro 𝒯 h𝒯
  have h := hHall 𝒯 h𝒯
  refine h.trans (le_of_eq ?_)
  congr 1
  apply Finset.biUnion_congr rfl
  intro S _
  exact rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S


theorem rc59_famCylBoxResidue_of_indepHall (h : rc59_IndepHall) : rc20_FamCylBoxResidue := by
  intro m 𝒜 ℬ
  exact rc59_wall_of_indepHall_pair 𝒜 ℬ (h m 𝒜 ℬ)


theorem rc59_reimerWprobCore_of_indepHall (h : rc59_IndepHall) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter
    (rc20_cylBoxReflInter_of_famCylBoxResidue (rc59_famCylBoxResidue_of_indepHall h))


open Classical in


theorem rc59_biUnion_nbhd_eq (𝒜 ℬ : Finset (Finset (Fin n))) (𝒯 : Finset (Finset (Fin n))) :
    𝒯.biUnion (rc59_nbhd 𝒜 ℬ) = 𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ) :=
  Finset.biUnion_congr rfl (fun S _ => rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S)

open Classical in

theorem rc59_indepHall_pair_iff (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ↔
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) := by
  constructor
  · intro h 𝒯 h𝒯; have := h 𝒯 h𝒯; rwa [rc59_biUnion_nbhd_eq] at this
  · intro h 𝒯 h𝒯; have := h 𝒯 h𝒯; rwa [rc59_biUnion_nbhd_eq]

open Classical in

theorem rc59_indepHall_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  (rc59_indepHall_pair_iff 𝒜 ℬ).mpr
    (rc33_hallOneSidedA_prop_of_bool 0 𝒜 ℬ (rc33_hallOneSidedA_fin0 𝒜 ℬ))

open Classical in

theorem rc59_indepHall_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  (rc59_indepHall_pair_iff 𝒜 ℬ).mpr
    (rc33_hallOneSidedA_prop_of_bool 1 𝒜 ℬ (rc33_hallOneSidedA_fin1 𝒜 ℬ))

open Classical in


theorem rc59_indepHall_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  (rc59_indepHall_pair_iff 𝒜 ℬ).mpr
    (rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ))

open Classical in


theorem rc59_wall_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc59_wall_of_indepHall_pair 𝒜 ℬ (rc59_indepHall_fin2 𝒜 ℬ)


open Classical in


theorem rc59_indepHall_fin3_refuter :
    ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card :=
  (rc59_indepHall_pair_iff rc32_A3 rc32_B3).mpr
    (rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter)

open Classical in


theorem rc59_wall_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) :=
  rc59_wall_of_indepHall_pair rc32_A3 rc32_B3 rc59_indepHall_fin3_refuter


theorem rc59_nbhd_proper_fin3 :
    rc59_nbhd rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3 := by
  rw [rc59_nbhd_eq_admOneSidedA]; exact rc33_admOneSidedA_proper_fin3


theorem rc59_reimerReflection_not_injective_fin3 :
    ((rc21_boxComp 3 rc32_A3 rc32_B3).biUnion
        (fun S => (rc21_symmWitComp 3 rc32_A3 rc32_B3 S).image (fun L => symmDiff S L))).card
      < (rc21_boxComp 3 rc32_A3 rc32_B3).card :=
  rc32_symmDiffMirror_fin3_refuted


theorem rc59_status :
    (rc59_IndepHall → ReimerWprobCore) ∧
    (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) ∧
    (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧
    (rc59_nbhd rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3) :=
  ⟨rc59_reimerWprobCore_of_indepHall, rc59_indepHall_fin3_refuter, rc59_wall_fin3_refuter,
    rc59_nbhd_proper_fin3⟩

end StatMech.Walls
