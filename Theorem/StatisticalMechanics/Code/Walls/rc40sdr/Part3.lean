/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Def.StatisticalMechanics.Code.Walls.rc40sdr.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in


theorem rc40_box_fin3 : rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}} := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc40_R0values_empty_zero_fin3 :
    rc40_R0valuesComp 3 rc40_Aref rc40_Bref {0} = {∅} := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc40_R0values_empty_one_fin3 :
    rc40_R0valuesComp 3 rc40_Aref rc40_Bref {1} = {∅} := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc40_R0values_biUnion_lt_box_fin3 :
    (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
        (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
      < (rc21_boxComp 3 rc40_Aref rc40_Bref).card := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc40_hallOneSidedA_holds_fin3 :
    rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true := by
  rw [rc40_Aref, rc40_Bref]; decide


open Classical in


theorem rc40_reimer_closes_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc18_CylBoxReflInter :=
  rc35_reimer_closes_of_oneSidedInjection h


set_option linter.unusedVariables false in
open Classical in


theorem rc40_reimer_r0insufficient :
    (∀ (S K L : Finset (Fin 3)), Disjoint K L → K ∪ L = univ →
        (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S)
      ∧ (∀ (K L : Finset (Fin 3)), Disjoint K L → K ∪ L = univ →
          ∀ {S S' : Finset (Fin 3)}, rc36_R0 S K L = rc36_R0 S' K L → S = S')
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)},
          S ∈ rc20_famCylBox 𝒜 ℬ →
          ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧
            (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
            (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
          rc40_R0valuesComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
            (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
          < (rc21_boxComp 3 rc40_Aref rc40_Bref).card)
      ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true)
      ∧ (rc35_OneSidedInjection → rc18_CylBoxReflInter) :=
  ⟨fun S K L hKL hcov => rc40_R0_recovers_of_cover S K L hKL hcov,
    fun K L hKL hcov _ _ h => rc40_R0_injOn_of_cover K L hKL hcov h,
    fun n 𝒜 ℬ _ hS => rc40_coveringPair_of_mem_box n 𝒜 ℬ hS,
    fun n 𝒜 ℬ S => rc40_R0values_subset_admOneSidedA n 𝒜 ℬ S,
    rc40_R0values_biUnion_lt_box_fin3,
    rc40_hallOneSidedA_holds_fin3,
    rc40_reimer_closes_of_oneSidedInjection⟩

end StatMech.Walls
