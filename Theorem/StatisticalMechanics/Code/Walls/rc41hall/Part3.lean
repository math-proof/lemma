/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Def.StatisticalMechanics.Code.Walls.rc41hall.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in


theorem rc41_commonWitness_collidingTrace_fin3 :
    rc41_hasCommonCoveringWitness 3 rc40_Aref rc40_Bref {{0}, {1}} = false := by
  rw [rc40_Aref, rc40_Bref, rc41_hasCommonCoveringWitness]; decide


theorem rc41_hallOneSidedA_holds_fin3 :
    rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true :=
  rc40_hallOneSidedA_holds_fin3


theorem rc41_hallBothSided_fails_fin3 :
    rc33_hallBothSided 3 rc32_A3 rc32_B3 = false :=
  rc33_hallBothSided_fin3_refuted


set_option linter.unusedVariables false in
open Classical in


theorem rc41_reimer_defectcounting :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)},
        (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) →
        Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n))) →
        𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))}
          {K : Finset (Fin n)},
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) →
          (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card)
      ∧ (rc33_HallOneSidedA ↔ rc41_DefectZero)
      ∧ (rc41_DefectZero → rc18_CylBoxReflInter)
      ∧ (rc41_hasCommonCoveringWitness 3 rc40_Aref rc40_Bref {{0}, {1}} = false)
      ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true)
      ∧ (rc33_hallBothSided 3 rc32_A3 rc32_B3 = false) :=
  ⟨fun n 𝒜 ℬ {𝒯} {K} hKA hKcB hinj =>
      rc41_hall_of_commonWitness_distinctTrace n 𝒜 ℬ hKA hKcB hinj,
    fun n 𝒜 ℬ {𝒯} {K} hKA hKcB => rc41_traceImage_le_biUnion n 𝒜 ℬ hKA hKcB,
    rc41_hallOneSidedA_iff_defectZero,
    rc41_reimer_closes_of_defectZero,
    rc41_commonWitness_collidingTrace_fin3,
    rc41_hallOneSidedA_holds_fin3,
    rc41_hallBothSided_fails_fin3⟩

end StatMech.Walls
