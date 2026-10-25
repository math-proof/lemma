/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part5
import Def.StatisticalMechanics.Code.Walls.rc21persupport
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc21_perSupportReflection_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc20_PerSupportReflection := by
  intro n 𝒜 ℬ
  obtain ⟨K, L, hwit, hinj⟩ := h n 𝒜 ℬ
  refine ⟨fun S => symmDiff S (L S), hinj, ?_⟩
  intro S hS
  obtain ⟨hKL, hKA, hLB⟩ := hwit S hS
  exact rc21_symmDiff_mem_reflInter hKL hKA hLB


theorem rc21_cylBoxReflInter_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc18_CylBoxReflInter :=
  rc20_perSupportReflection_iff_cylBoxReflInter.mp
    (rc21_perSupportReflection_of_symmDiffReflection h)


open Classical in


theorem rc21_localRefl_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L R : Finset α}
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)
    (hRK : R ∩ K = S ∩ K) (hRL : Rᶜ ∩ L = S ∩ L) :
    R ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  exact ⟨hKA R hRK, hLB Rᶜ hRL⟩


end StatMech.Walls
