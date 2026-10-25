/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Def.StatisticalMechanics.Code.Walls.rc42multiwitness.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc42_biUnionCovering_le_biUnion (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) :
    (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card
      ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  refine Finset.card_le_card (Finset.biUnion_subset.mpr ?_)
  intro S hS
  exact (rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S).trans
    (Finset.subset_biUnion_of_mem (rc33_admOneSidedA n 𝒜 ℬ) hS)

open Classical in


theorem rc42_defectZero_of_hallCovering (h : rc42_HallCovering) : rc41_DefectZero := by
  intro n 𝒜 ℬ 𝒯 h𝒯
  exact (h n 𝒜 ℬ 𝒯 h𝒯).trans (rc42_biUnionCovering_le_biUnion n 𝒜 ℬ 𝒯)

open Classical in


theorem rc42_reimer_closes_of_hallCovering (h : rc42_HallCovering) : rc18_CylBoxReflInter :=
  rc41_reimer_closes_of_defectZero (rc42_defectZero_of_hallCovering h)


open Classical in


theorem rc42_slice_subset_admCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKw : ∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ)
    {S : Finset (Fin n)} (hS : S ∈ 𝒯) :
    rc35_traceSlice 𝒜 ℬ K S ⊆ rc42_admCovering n 𝒜 ℬ S := by
  intro R hR
  rw [rc42_admCovering, Finset.mem_biUnion]
  exact ⟨K, by rw [rc42_cwits, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hKw S hS⟩, hR⟩

open Classical in


theorem rc42_traceImage_le_biUnionCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKw : ∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ) :
    (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  
  have himg : 𝒯.image (fun S => S ∩ K)
      = (𝒯.image (fun S => rc36_R0 S K Kᶜ)).image (fun R => R ∩ K) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro S _
    simp only [Function.comp]
    exact (rc41_R0cover_inter S K).symm
  calc (𝒯.image (fun S => S ∩ K)).card
      = ((𝒯.image (fun S => rc36_R0 S K Kᶜ)).image (fun R => R ∩ K)).card := by rw [himg]
    _ ≤ (𝒯.image (fun S => rc36_R0 S K Kᶜ)).card := Finset.card_image_le
    _ ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
        refine Finset.card_le_card ?_
        intro R hR
        rw [Finset.mem_image] at hR
        obtain ⟨S, hS, rfl⟩ := hR
        refine Finset.mem_biUnion.mpr ⟨S, hS, ?_⟩
        
        refine rc42_slice_subset_admCovering n 𝒜 ℬ hKw hS ?_
        exact rc36_R0_mem_traceSlice 𝒜 ℬ disjoint_compl_right
          ((rc20_traceClass_subset_iff n K S 𝒜).mp (hKw S hS).1)
          ((rc20_traceClass_subset_iff n Kᶜ S ℬ).mp (hKw S hS).2)

open Classical in


theorem rc42_card_biUnion_traceSlice_eq_sum (𝒜 ℬ : Finset (Finset α)) (K : Finset α)
    (𝒯 : Finset (Finset α)) :
    ((𝒯.image (fun S => S ∩ K)).biUnion (fun t => rc35_traceSlice 𝒜 ℬ K t)).card
      = ∑ t ∈ 𝒯.image (fun S => S ∩ K), (rc35_traceSlice 𝒜 ℬ K t).card := by
  refine Finset.card_biUnion ?_
  intro t ht t' ht' hne
  
  rw [Finset.mem_coe, Finset.mem_image] at ht ht'
  obtain ⟨S, _, rfl⟩ := ht
  obtain ⟨S', _, rfl⟩ := ht'
  refine rc42_traceSlice_disjoint_of_ne 𝒜 ℬ K (S ∩ K) (S' ∩ K) ?_
  
  rw [Finset.inter_assoc, Finset.inter_self, Finset.inter_assoc, Finset.inter_self]
  exact hne


end StatMech.Walls
