/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
import Def.StatisticalMechanics.Code.Walls.rc28cylrec
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc28_mem_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc28_famCylBoxE E 𝒜 ℬ ↔ S ⊆ E ∧ ∃ K L : Finset α, Disjoint K L ∧
      (∀ T : Finset α, T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ⊆ E → T ∩ L = S ∩ L → T ∈ ℬ) := by
  simp only [rc28_famCylBoxE, Finset.mem_filter, Finset.mem_powerset]


end StatMech.Walls
