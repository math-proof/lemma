/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc34butterfly.Part2
import Def.StatisticalMechanics.Code.Walls.rc35hallproof
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc35_slice_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K : Finset (Fin n)} (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) :
    rc35_traceSlice 𝒜 ℬ K S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc35_traceSlice, Finset.mem_filter] at hR
  obtain ⟨hRri, hRK⟩ := hR
  rw [rc20_mem_reflInter] at hRri
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨Finset.mem_univ _, hRri.1, hRri.2, K, Finset.mem_univ _,
    (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, hRK⟩


end StatMech.Walls
