/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc49doubled
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc49_jointImage_inter_K (S K L : Finset α) (hKL : Disjoint K L) :
    rc49_jointImage S K L ∩ K = S ∩ K := by
  rw [rc49_jointImage]
  ext a
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
  constructor
  · rintro ⟨(⟨_, _⟩ | ⟨haL, _⟩) | ⟨_, haKL⟩, haK⟩
    · exact ⟨‹a ∈ S›, haK⟩
    · exact absurd haK (Finset.disjoint_right.mp hKL haL)
    · exact absurd (Or.inl haK) haKL
  · rintro ⟨haS, haK⟩
    exact ⟨Or.inl (Or.inl ⟨haS, haK⟩), haK⟩


theorem rc49_jointImage_compl_inter_L (S K L : Finset α) (hKL : Disjoint K L) :
    (rc49_jointImage S K L)ᶜ ∩ L = S ∩ L := by
  rw [rc49_jointImage]
  ext a
  constructor
  · intro ha
    rw [Finset.mem_inter, Finset.mem_compl] at ha
    obtain ⟨hnot, haL⟩ := ha
    rw [Finset.mem_inter]
    refine ⟨?_, haL⟩
    by_contra haS
    exact hnot (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_inter.mpr ⟨haL, Finset.mem_compl.mpr haS⟩)))
  · intro ha
    rw [Finset.mem_inter] at ha
    obtain ⟨haS, haL⟩ := ha
    rw [Finset.mem_inter, Finset.mem_compl]
    refine ⟨?_, haL⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h1 | h2
      · exact Finset.disjoint_left.mp hKL (Finset.mem_inter.mp h1).2 haL
      · exact (Finset.mem_compl.mp (Finset.mem_inter.mp h2).2) haS
    · exact (Finset.mem_compl.mp (Finset.mem_inter.mp h).2)
        (Finset.mem_union_right _ haL)

open Classical in


theorem rc49_jointImage_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L)
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  refine ⟨hKA _ (rc49_jointImage_inter_K S K L hKL), hLB _ ?_⟩
  rw [rc49_jointImage_compl_inter_L S K L hKL]


end StatMech.Walls
