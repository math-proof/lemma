/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part5
import Def.StatisticalMechanics.Code.Walls.rc21persupport.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc21_boxComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc21_boxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  rw [← rc20_famCylBoxComp_eq]
  rfl

open Classical in


theorem rc21_admComp_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc21_admComp n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc21_admComp, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, K, _, L, _, hKL, hKA, hLB, hRK, hRL⟩ := hR
  exact rc21_localRefl_mem_reflInter
    ((rc20_traceClass_subset_iff n K S 𝒜).mp hKA)
    ((rc20_traceClass_subset_iff n L S ℬ).mp hLB) hRK hRL


end StatMech.Walls
