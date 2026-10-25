/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Walls.rc22doublecover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc22_mem_complPairs (𝒜 ℬ : Finset (Finset α)) (p : Finset α × Finset α) :
    p ∈ rc22_complPairs 𝒜 ℬ ↔
      p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ ∧ Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = univ := by
  rw [rc22_complPairs, Finset.mem_filter, Finset.mem_product]
  tauto


theorem rc22_compl_of_disjoint_union {S T : Finset α} (hd : Disjoint S T) (hu : S ∪ T = univ) :
    Sᶜ = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_compl] at hx
    have : x ∈ S ∪ T := by rw [hu]; exact Finset.mem_univ x
    rw [Finset.mem_union] at this
    exact this.resolve_left hx
  · have hcard : #S + #T = Fintype.card α := by
      rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]
    have hcompl_card : #Sᶜ = Fintype.card α - #S := by rw [Finset.card_compl]
    omega

open Classical in


theorem rc22_card_reflInter_eq_complPairs (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc22_complPairs 𝒜 ℬ) := by
  apply Finset.card_bij (fun S _ => (S, Sᶜ))
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc22_mem_complPairs]
    exact ⟨hS.1, hS.2, disjoint_compl_right, by simp⟩
  · intro S _ S' _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1
  · intro p hp
    rw [rc22_mem_complPairs] at hp
    obtain ⟨h1, h2, hd, hu⟩ := hp
    have hcompl : p.1ᶜ = p.2 := rc22_compl_of_disjoint_union hd hu
    refine ⟨p.1, ?_, ?_⟩
    · rw [rc20_mem_reflInter]
      exact ⟨h1, by rw [hcompl]; exact h2⟩
    · rw [hcompl]


theorem rc22_complPairs_eq_filter (𝒜 ℬ : Finset (Finset α)) :
    rc22_complPairs 𝒜 ℬ
      = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => p.1 ∪ p.2 = univ) := by
  rw [rc22_complPairs, Finset.filter_filter]


theorem rc22_reflInter_le_dpairsCount (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ := by
  rw [rc22_card_reflInter_eq_complPairs, rc22_complPairs_eq_filter, dpairsCount]
  exact Finset.card_filter_le _ _


end StatMech.Walls
