/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Def.StatisticalMechanics.Code.Walls.rc42multiwitness.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc42_hallCovering_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc42_hallCovering n 𝒜 ℬ = true) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  rw [rc42_hallCovering, decide_eq_true_eq, rc21_boxComp_eq] at h
  intro 𝒯 h𝒯
  have := h 𝒯 h𝒯
  rwa [show 𝒯.biUnion (rc42_admCoveringComp n 𝒜 ℬ) = 𝒯.biUnion (rc42_admCovering n 𝒜 ℬ) from
    Finset.biUnion_congr rfl (fun S _ => rc42_admCoveringComp_eq n 𝒜 ℬ S)] at this


set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in


theorem rc42_hallCovering_holds_fin3 :
    rc42_hallCovering 3 rc40_Aref rc40_Bref = true := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in


theorem rc42_hallCovering_holds_A3ex :
    rc42_hallCovering 3 rc36_A3ex rc36_B3ex = true := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 6000 in


theorem rc42_admCovering_proper_fin3 :
    rc42_admCoveringComp 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅
      ⊂ rc33_admOneSidedA 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅ := by
  decide


theorem rc42_R0_insufficient_fin3 :
    (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
        (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
      < (rc21_boxComp 3 rc40_Aref rc40_Bref).card :=
  rc40_R0values_biUnion_lt_box_fin3


set_option linter.unusedVariables false in
open Classical in


theorem rc42_reimer_coveringwitness :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (K S S' : Finset (Fin 3)), S ∩ K ≠ S' ∩ K →
        Disjoint (rc35_traceSlice 𝒜 ℬ K S) (rc35_traceSlice 𝒜 ℬ K S'))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
          rc42_admCovering n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (rc42_HallCovering → rc41_DefectZero)
      ∧ (rc42_HallCovering → rc18_CylBoxReflInter)
      ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true)
      ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
            (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
          < (rc21_boxComp 3 rc40_Aref rc40_Bref).card)
      ∧ (rc42_admCoveringComp 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅
          ⊂ rc33_admOneSidedA 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅) :=
  ⟨fun 𝒜 ℬ K S S' h => rc42_traceSlice_disjoint_of_ne 𝒜 ℬ K S S' h,
    fun n 𝒜 ℬ S => rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S,
    rc42_defectZero_of_hallCovering,
    rc42_reimer_closes_of_hallCovering,
    rc42_hallCovering_holds_fin3,
    rc42_R0_insufficient_fin3,
    rc42_admCovering_proper_fin3⟩

end StatMech.Walls
