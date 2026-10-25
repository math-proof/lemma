/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
import Def.StatisticalMechanics.Code.Walls.rc20reflection
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc20_cylBoxSupp_eq_famCylBox (A B : Set (ConfigSpace α)) :
    rc18_cylBoxSupp A B = rc20_famCylBox (eventFamily A) (eventFamily B) := by
  ext S
  rw [rc18_cylBoxSupp, rc20_famCylBox, Finset.mem_filter, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc20_cylinder_subset_iff_family A K S).mp hKA,
      (rc20_cylinder_subset_iff_family B L S).mp hLB⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc20_cylinder_subset_iff_family A K S).mpr hKA,
      (rc20_cylinder_subset_iff_family B L S).mpr hLB⟩

open Classical in


theorem rc20_mem_reflInter (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_reflInter 𝒜 ℬ ↔ S ∈ 𝒜 ∧ Sᶜ ∈ ℬ := by
  rw [rc10_reflInter, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩


end StatMech.Walls
