/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc35hallproof.Part3
import Def.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in


theorem rc36_neighbour_empty_singleton_fin3 :
    rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ = {{1, 2}} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in


theorem rc36_neighbour_one_fin3 :
    rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1} = {{1, 2}, {0, 1, 2}} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in

theorem rc36_box_fin3 :
    rc21_boxComp 3 rc36_A3ex rc36_B3ex = {∅, {1}} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in


theorem rc36_minNeighbour_lt_box_fin3 :
    (rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅).card < (rc21_boxComp 3 rc36_A3ex rc36_B3ex).card := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in


theorem rc36_neighbour_empty_ssubset_one_fin3 :
    rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ ⊂ rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc36_hallOneSidedA_holds_fin3 :
    rc33_hallOneSidedA 3 rc36_A3ex rc36_B3ex = true := by
  rw [rc36_A3ex, rc36_B3ex]; decide


set_option linter.unusedVariables false in
open Classical in


theorem rc36_reimer_defectcounting :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S K L : Finset (Fin n)},
        Disjoint K L → (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) →
        rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)},
          S ∈ rc20_famCylBox 𝒜 ℬ → (rc33_admOneSidedA n 𝒜 ℬ S).Nonempty)
      ∧ (∀ (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n))
          {K K' : Finset (Fin n)}, K ∈ rc35_awitsA n 𝒜 S → K ⊆ K' → K' ∈ rc35_awitsA n 𝒜 S)
      ∧ (rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅
          ⊂ rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1})
      ∧ ((rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅).card
          < (rc21_boxComp 3 rc36_A3ex rc36_B3ex).card)
      ∧ (rc33_hallOneSidedA 3 rc36_A3ex rc36_B3ex = true) :=
  ⟨fun n 𝒜 ℬ _ _ _ hKL hKA hLB => rc36_R0_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB,
    fun n 𝒜 ℬ _ hS => rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS,
    fun n 𝒜 S _ _ hK hKK' => rc36_awitsA_upward_closed n 𝒜 S hK hKK',
    rc36_neighbour_empty_ssubset_one_fin3,
    rc36_minNeighbour_lt_box_fin3,
    rc36_hallOneSidedA_holds_fin3⟩

end StatMech.Walls
