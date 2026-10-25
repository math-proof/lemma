/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc32reflwitness.Part2
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc33_hallOneSidedA_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc33_hallOneSidedA n 𝒜 ℬ = true) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  rw [rc33_hallOneSidedA, decide_eq_true_eq, rc21_boxComp_eq] at h
  exact h


theorem rc33_hallOneSidedA_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    rc33_hallOneSidedA 0 𝒜 ℬ = true := by revert 𝒜 ℬ; decide


theorem rc33_hallOneSidedA_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    rc33_hallOneSidedA 1 𝒜 ℬ = true := by revert 𝒜 ℬ; decide

set_option maxHeartbeats 4000000 in


theorem rc33_hallOneSidedA_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    rc33_hallOneSidedA 2 𝒜 ℬ = true := by revert 𝒜 ℬ; decide

open Classical in


theorem rc33_wall_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc33_wall_of_hallOneSidedA 2 𝒜 ℬ (rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ))


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc33_hallOneSidedA_fin3_refuter :
    rc33_hallOneSidedA 3 rc32_A3 rc32_B3 = true := by
  rw [rc32_A3, rc32_B3]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc33_hallBothSided_fin3_refuted :
    rc33_hallBothSided 3 rc32_A3 rc32_B3 = false := by
  rw [rc32_A3, rc32_B3]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc33_admOneSidedA_proper_fin3 :
    rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3 := by
  rw [rc32_A3, rc32_B3, ← rc20_reflInterComp_eq]; decide


theorem rc33_wall_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) :=
  rc33_wall_of_hallOneSidedA 3 rc32_A3 rc32_B3
    (rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter)


set_option linter.unusedVariables false in
open Classical in


theorem rc33_reimer_nonlocal :
    (rc33_HallOneSidedA → rc20_PerSupportReflection)
      ∧ (rc33_HallOneSidedA → rc18_CylBoxReflInter)
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc33_hallOneSidedA 3 rc32_A3 rc32_B3 = true)
      ∧ (rc33_hallBothSided 3 rc32_A3 rc32_B3 = false)
      ∧ (rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3) :=
  ⟨rc33_perSupportReflection_of_hallOneSidedA,
    rc33_reimer_closes_of_hallOneSidedA,
    rc33_wall_fin2,
    rc33_hallOneSidedA_fin3_refuter,
    rc33_hallBothSided_fin3_refuted,
    rc33_admOneSidedA_proper_fin3⟩

end StatMech.Walls
