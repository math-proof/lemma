/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc34butterfly.Part2
import Def.StatisticalMechanics.Code.Walls.rc35hallproof.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc35_oneSidedInjection_iff_hallOneSidedA :
    rc35_OneSidedInjection ↔ rc33_HallOneSidedA := by
  constructor
  · intro h n 𝒜 ℬ
    exact (rc35_hallOneSidedA_iff_injection n 𝒜 ℬ).mpr (h n 𝒜 ℬ)
  · intro h n 𝒜 ℬ
    exact (rc35_hallOneSidedA_iff_injection n 𝒜 ℬ).mp (h n 𝒜 ℬ)

open Classical in


theorem rc35_famCylBoxResidue_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc20_FamCylBoxResidue :=
  rc33_famCylBoxResidue_of_hallOneSidedA (rc35_oneSidedInjection_iff_hallOneSidedA.mp h)

open Classical in


theorem rc35_reimer_closes_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc18_CylBoxReflInter :=
  rc33_reimer_closes_of_hallOneSidedA (rc35_oneSidedInjection_iff_hallOneSidedA.mp h)

open Classical in


theorem rc35_oneSidedInjection_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∃ f : Finset (Fin 2) → Finset (Fin 2),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin 2))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA 2 𝒜 ℬ S :=
  (rc35_hallOneSidedA_iff_injection 2 𝒜 ℬ).mp
    (rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ))

open Classical in


theorem rc35_oneSidedInjection_fin3_refuter :
    ∃ f : Finset (Fin 3) → Finset (Fin 3),
      Set.InjOn f (rc20_famCylBox rc32_A3 rc32_B3 : Set (Finset (Fin 3))) ∧
      ∀ S ∈ rc20_famCylBox rc32_A3 rc32_B3, f S ∈ rc33_admOneSidedA 3 rc32_A3 rc32_B3 S :=
  (rc35_hallOneSidedA_iff_injection 3 rc32_A3 rc32_B3).mp
    (rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter)


theorem rc35_box_not_subset_reflInter_fin2 :
    ¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {1}})
        ⊆ rc10_reflInter ({∅, {0}}) ({∅, {1}})) := by
  rw [← rc21_boxComp_eq, ← rc20_reflInterComp_eq]
  decide


theorem rc35_self_not_admissible_fin2 :
    (∅ : Finset (Fin 2)) ∉ rc33_admOneSidedA 2 ({∅, {0}}) ({∅, {1}}) ∅ := by
  decide


theorem rc35_minNeighbour_lt_box_fin2 :
    (rc33_admOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) {0}).card
      < (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2)))
          ({∅, {0}, {1}, {0, 1}})).card := by
  rw [← rc21_boxComp_eq]
  decide


theorem rc35_hallOneSidedA_holds_minWitness_fin2 :
    rc33_hallOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) = true := by
  decide


set_option linter.unusedVariables false in
open Classical in


theorem rc35_reimer_hallconcrete :
    (rc35_OneSidedInjection ↔ rc33_HallOneSidedA)
      ∧ (rc35_OneSidedInjection → rc18_CylBoxReflInter)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S K : Finset (Fin n)),
          (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
          rc35_traceSlice 𝒜 ℬ K S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {1}})
          ⊆ rc10_reflInter ({∅, {0}}) ({∅, {1}})))
      ∧ ((rc33_admOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) {0}).card
          < (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2)))
              ({∅, {0}, {1}, {0, 1}})).card)
      ∧ (rc33_hallOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) = true) :=
  ⟨rc35_oneSidedInjection_iff_hallOneSidedA,
    rc35_reimer_closes_of_oneSidedInjection,
    fun n 𝒜 ℬ S K hKA => rc35_slice_subset_admOneSidedA n 𝒜 ℬ hKA,
    rc35_box_not_subset_reflInter_fin2,
    rc35_minNeighbour_lt_box_fin2,
    rc35_hallOneSidedA_holds_minWitness_fin2⟩

end StatMech.Walls
