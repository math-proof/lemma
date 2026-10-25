/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc14reimerinduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Def.StatisticalMechanics.Code.Walls.rc14reimerinduct
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc14_mem_boxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc14_boxE E 𝒜 ℬ ↔
      S ⊆ E ∧ ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ := by
  simp only [rc14_boxE, Finset.mem_filter, Finset.mem_powerset]

open Classical in

theorem rc14_mem_reflE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc14_reflE E 𝒜 ℬ ↔ S ⊆ E ∧ S ∈ 𝒜 ∧ E \ S ∈ ℬ := by
  simp only [rc14_reflE, Finset.mem_filter, Finset.mem_powerset]

end StatMech.Walls
