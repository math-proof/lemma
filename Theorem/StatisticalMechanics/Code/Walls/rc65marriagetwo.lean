/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc64consolidation.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc65_nbhd_nonempty (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) : (rc59_nbhd 𝒜 ℬ S).Nonempty := by
  rw [rc59_nbhd_eq_admOneSidedA]
  exact rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS

open Classical in


theorem rc65_pair_biUnion (𝒜 ℬ : Finset (Finset (Fin n))) (S₁ S₂ : Finset (Fin n)) :
    ({S₁, S₂} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)
      = rc59_nbhd 𝒜 ℬ S₁ ∪ rc59_nbhd 𝒜 ℬ S₂ := by
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]


end StatMech.Walls
