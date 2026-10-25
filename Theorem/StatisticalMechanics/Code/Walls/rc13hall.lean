/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Def.StatisticalMechanics.Code.Walls.rc13hall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc13_mem_adm (𝒜 ℬ : Finset (Finset α)) (S R : Finset α) :
    R ∈ rc13_adm 𝒜 ℬ S ↔ ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ ∧ T ⊆ R ∧ Disjoint R (S \ T) := by
  simp only [rc13_adm, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in


theorem rc13_adm_subset_reflInter (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (S : Finset α) : rc13_adm 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc13_mem_adm] at hR
  obtain ⟨T, _, hT, hST, hTR, hdisj⟩ := hR
  exact rc12_reflConstraint_mem_reflInter 𝒜 ℬ h𝒜 hℬ hT hST hTR hdisj


end StatMech.Walls
