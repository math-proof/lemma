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
import Def.StatisticalMechanics.Code.Walls.rc49doubled.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc49_neighbourhood_subset_reflInter (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    rc49_neighbourhood 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ :=
  Finset.filter_subset _ _

open Classical in


theorem rc49_neighbourhood_nonempty {𝒜 ℬ : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (rc49_neighbourhood 𝒜 ℬ S).Nonempty := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  refine ⟨rc49_jointImage S K L, ?_⟩
  rw [rc49_neighbourhood, Finset.mem_filter]
  exact ⟨rc49_jointImage_mem_reflInter hKL hKA hLB, K, L, hKL, hKA, hLB, rfl⟩


end StatMech.Walls
