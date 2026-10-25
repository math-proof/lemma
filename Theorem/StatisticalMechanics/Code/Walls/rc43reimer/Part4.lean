/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc43reimer.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc43_globalCommonWitness_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc43_globalCommonWitness n 𝒜 ℬ = true) :
    rc43_GlobalCommonWitness n 𝒜 ℬ := by
  rw [rc43_globalCommonWitness, decide_eq_true_eq, rc21_boxComp_eq] at h
  obtain ⟨K, hKA, hKcB⟩ := h
  refine ⟨K, ?_, ?_⟩
  · intro S hS T hT
    exact (rc20_traceClass_subset_iff n K S 𝒜).mp (hKA S hS) T hT
  · intro S hS T hT
    exact (rc20_traceClass_subset_iff n Kᶜ S ℬ).mp (hKcB S hS) T hT

set_option maxRecDepth 4000 in


theorem rc43_globalCommonWitness_refuter_false :
    rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false := by
  rw [rc40_Aref, rc40_Bref, rc43_globalCommonWitness]; decide


theorem rc43_globalCommonWitness_univ_fin2 :
    rc43_globalCommonWitness 2 Finset.univ Finset.univ = true := by
  decide

open Classical in


theorem rc43_residue_named :
    (rc43_GlobalCommonWitnessAll → rc18_CylBoxReflInter)
      ∧ (rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false)
      ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true) :=
  ⟨rc43_reimer_closes_of_globalCommonWitnessAll,
    rc43_globalCommonWitness_refuter_false,
    rc42_hallCovering_holds_fin3⟩


set_option linter.unusedVariables false in
open Classical in


theorem rc43_reimer_symmetry_and_globalwitness :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))}
            {K : Finset (Fin n)},
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) →
          𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
          rc43_GlobalCommonWitness n 𝒜 ℬ →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc43_GlobalCommonWitnessAll → rc18_CylBoxReflInter)
      ∧ (rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false)
      ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true)
      ∧ (rc43_globalCommonWitness 2 Finset.univ Finset.univ = true) :=
  ⟨fun 𝒜 ℬ => rc43_famCylBox_symm 𝒜 ℬ,
    fun 𝒜 ℬ => rc43_reflInter_card_transpose 𝒜 ℬ,
    fun n 𝒜 ℬ {𝒯} {K} hKA hKcB => rc43_hall_of_commonCoveringWitness n 𝒜 ℬ hKA hKcB,
    fun n 𝒜 ℬ h => rc43_famCylBox_le_reflInter_of_globalCommonWitness n 𝒜 ℬ h,
    rc43_reimer_closes_of_globalCommonWitnessAll,
    rc43_globalCommonWitness_refuter_false,
    rc42_hallCovering_holds_fin3,
    rc43_globalCommonWitness_univ_fin2⟩

end StatMech.Walls
