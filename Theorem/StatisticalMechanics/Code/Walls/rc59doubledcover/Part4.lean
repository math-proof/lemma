/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc59doubledcover.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc59_nbhd_eq_admOneSidedA (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc59_nbhd 𝒜 ℬ S = rc33_admOneSidedA n 𝒜 ℬ S := by
  rw [rc59_nbhd, rc59_leftFactor, rc59_rightFactor, ← rc37_admOneSidedA_eq_inter]


theorem rc59_rightFactor_indep (ℬ : Finset (Finset (Fin n))) (S S' : Finset (Fin n)) :
    rc59_rightFactor ℬ = rc59_rightFactor ℬ ∧
      (rc59_nbhd 𝒜 ℬ S = rc59_leftFactor 𝒜 S ∩ rc59_rightFactor ℬ ∧
       rc59_nbhd 𝒜 ℬ S' = rc59_leftFactor 𝒜 S' ∩ rc59_rightFactor ℬ) := by
  exact ⟨rfl, rfl, rfl⟩


theorem rc59_reflInter_eq_inter_rightFactor (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc59_rightFactor ℬ := by
  ext R
  rw [rc20_mem_reflInter, rc59_rightFactor, rc37_rightMem, Finset.mem_inter, Finset.mem_filter,
    decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, Finset.mem_univ _, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

end StatMech.Walls
