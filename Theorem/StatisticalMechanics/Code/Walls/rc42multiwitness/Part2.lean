/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Def.StatisticalMechanics.Code.Walls.rc42multiwitness
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc42_cwits_subset_awitsA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc42_cwits n 𝒜 ℬ S ⊆ rc35_awitsA n 𝒜 S := by
  intro K hK
  rw [rc42_cwits, Finset.mem_filter] at hK
  rw [rc35_awitsA, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hK.2.1⟩

end StatMech.Walls
