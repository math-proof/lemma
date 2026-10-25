/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Def.StatisticalMechanics.Code.Walls.rc40sdr
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc40_R0values_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    rc40_R0valuesComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc40_R0valuesComp, Finset.mem_image] at hR
  obtain ⟨KL, hKL, rfl⟩ := hR
  rw [Finset.mem_filter, decide_eq_true_eq] at hKL
  obtain ⟨_, hdis, hKA, hLB⟩ := hKL
  exact rc36_R0_mem_admOneSidedA n 𝒜 ℬ hdis
    ((rc20_traceClass_subset_iff n KL.1 S 𝒜).mp hKA)
    ((rc20_traceClass_subset_iff n KL.2 S ℬ).mp hLB)


end StatMech.Walls
