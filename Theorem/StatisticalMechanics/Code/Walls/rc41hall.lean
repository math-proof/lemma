/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc41_R0cover_inter (S K : Finset α) : rc36_R0 S K Kᶜ ∩ K = S ∩ K :=
  rc36_R0_inter_left S K Kᶜ disjoint_compl_right


theorem rc41_R0cover_traceEq (S S' K : Finset α) (h : rc36_R0 S K Kᶜ = rc36_R0 S' K Kᶜ) :
    S ∩ K = S' ∩ K := by
  have := congrArg (· ∩ K) h
  simpa only [rc41_R0cover_inter] using this


theorem rc41_R0cover_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K : Finset (Fin n)} (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    rc36_R0 S K Kᶜ ∈ rc33_admOneSidedA n 𝒜 ℬ S :=
  rc36_R0_mem_admOneSidedA n 𝒜 ℬ disjoint_compl_right hKA hKcB


open Classical in


theorem rc41_hall_of_commonWitness_distinctTrace (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ)
    (hinj : Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n)))) :
    𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  refine Finset.card_le_card_of_injOn (fun S => rc36_R0 S K Kᶜ) ?_ ?_
  · 
    intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨S, hS, rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ (hKA S hS) (hKcB S hS)⟩
  · 
    intro S hS S' hS' h
    exact hinj hS hS' (rc41_R0cover_traceEq S S' K h)


open Classical in


theorem rc41_traceImage_le_biUnion (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  
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
    _ ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
        refine Finset.card_le_card ?_
        intro R hR
        rw [Finset.mem_image] at hR
        obtain ⟨S, hS, rfl⟩ := hR
        exact Finset.mem_biUnion.mpr
          ⟨S, hS, rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ (hKA S hS) (hKcB S hS)⟩


end StatMech.Walls
