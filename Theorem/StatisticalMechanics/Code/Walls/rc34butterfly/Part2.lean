/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc34butterfly
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxHeartbeats 1000000 in


theorem rc34_card_boxDoubled_A3B3 :
    (boxDoubled rc34_A3 rc34_B3).card = 2 := by
  rw [card_boxDoubled, rc34_A3, rc34_B3]; decide

set_option maxHeartbeats 1000000 in


theorem rc34_card_boxDoubled_compressed :
    (boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3)).card = 4 := by
  rw [card_boxDoubled, rc34_A3, rc34_B3]; decide


theorem rc34_doubleCompress_ne_componentBox :
    doubleCompress 0 (boxDoubled rc34_A3 rc34_B3)
      ≠ boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3) := by
  intro h
  have hL : (doubleCompress 0 (boxDoubled rc34_A3 rc34_B3)).card = 2 := by
    rw [doubleCompress_card, rc34_card_boxDoubled_A3B3]
  have hR := rc34_card_boxDoubled_compressed
  rw [h] at hL
  rw [hL] at hR
  exact absurd hR (by norm_num)


theorem rc34_localReflHall_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc21_localReflSearch n 𝒜 ℬ = true) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card := by
  rw [rc21_localReflSearch, decide_eq_true_eq, rc21_boxComp_eq] at h
  exact h


theorem rc34_localReflSearch_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    rc21_localReflSearch 1 𝒜 ℬ = true := by revert 𝒜 ℬ; decide

open Classical in


theorem rc34_wall_fin1_via_subgraph (𝒜 ℬ : Finset (Finset (Fin 1))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc33_wall_of_hallOneSidedA 1 𝒜 ℬ
    (rc34_hallOneSidedA_of_localReflHall 1 𝒜 ℬ
      (rc34_localReflHall_prop_of_bool 1 𝒜 ℬ (rc34_localReflSearch_fin1 𝒜 ℬ)))


set_option linter.unusedVariables false in
open Classical in


theorem rc34_reimer_butterfly :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
        rc21_admComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
          (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
            𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card) →
          (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
            𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (doubleCompress 0 (boxDoubled rc34_A3 rc34_B3)
          ≠ boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3)) :=
  ⟨rc34_admComp_subset_admOneSidedA,
    rc34_hallOneSidedA_of_localReflHall,
    rc34_wall_fin1_via_subgraph,
    rc34_doubleCompress_ne_componentBox⟩

end StatMech.Walls
