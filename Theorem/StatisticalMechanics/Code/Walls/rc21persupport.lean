/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc21_mem_famCylBox (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔ ∃ K L : Finset α, Disjoint K L ∧
      (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) := by
  rw [rc20_famCylBox, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩


omit [Fintype α] in


theorem rc21_symmDiff_inter_left (S K L : Finset α) (hKL : Disjoint K L) :
    (symmDiff S L) ∩ K = S ∩ K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h, hxK⟩
    refine ⟨?_, hxK⟩
    rcases h with ⟨hS, _⟩ | ⟨hL, _⟩
    · exact hS
    · exact absurd hxK (Finset.disjoint_right.mp hKL hL)
  · rintro ⟨hxS, hxK⟩
    have hxL : x ∉ L := Finset.disjoint_left.mp hKL hxK
    exact ⟨Or.inl ⟨hxS, hxL⟩, hxK⟩


theorem rc21_symmDiff_compl_inter_right (S L : Finset α) :
    (symmDiff S L)ᶜ ∩ L = S ∩ L := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h, hxL⟩
    refine ⟨?_, hxL⟩
    by_contra hxS
    exact h (Or.inr ⟨hxL, hxS⟩)
  · rintro ⟨hxS, hxL⟩
    refine ⟨?_, hxL⟩
    rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h hxL
    · exact h hxS

open Classical in


theorem rc21_symmDiff_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    symmDiff S L ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  refine ⟨hKA _ (rc21_symmDiff_inter_left S K L hKL), hLB _ ?_⟩
  exact rc21_symmDiff_compl_inter_right S L


end StatMech.Walls
