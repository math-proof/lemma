/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Def.StatisticalMechanics.Code.Walls.rc12reimerinjection
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc12_mem_upGen (L0 S : Finset α) : S ∈ rc12_upGen L0 ↔ L0 ⊆ S := by
  simp [rc12_upGen]

open Classical in

theorem rc12_upGen_isUpper (L0 : Finset α) :
    IsUpperSet ((rc12_upGen L0 : Finset (Finset α)) : Set (Finset α)) := by
  intro S T hST hS
  simp only [Finset.mem_coe, rc12_mem_upGen] at hS ⊢
  exact hS.trans (Finset.le_iff_subset.mp hST)


open Classical in


theorem rc12_reflConstraint_mem_reflInter (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    {S T R : Finset α} (hT : T ∈ 𝒜) (hST : S \ T ∈ ℬ) (hTR : T ⊆ R)
    (hdisj : Disjoint R (S \ T)) : R ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc11_mem_reflInter]
  refine ⟨h𝒜 (Finset.le_iff_subset.mpr hTR) hT, ?_⟩
  apply hℬ _ hST
  rw [Finset.le_iff_subset]
  intro a ha
  rw [Finset.mem_compl]
  exact fun haR => (Finset.disjoint_left.mp hdisj haR) ha


end StatMech.Walls
