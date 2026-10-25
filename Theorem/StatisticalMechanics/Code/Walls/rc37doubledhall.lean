/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc37doubledhall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc37_admOneSidedA_eq_inter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ rc37_rightMem n ℬ := by
  ext R
  rw [rc33_admOneSidedA, rc37_admLeft, rc37_rightMem, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq,
    decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hRA, hRB, K, hK, hKA, hRK⟩
    exact ⟨⟨Finset.mem_univ _, hRA, K, hK, hKA, hRK⟩, ⟨Finset.mem_univ _, hRB⟩⟩
  · rintro ⟨⟨_, hRA, K, hK, hKA, hRK⟩, ⟨_, hRB⟩⟩
    exact ⟨Finset.mem_univ _, hRA, hRB, K, hK, hKA, hRK⟩


theorem rc37_rightMem_indep (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S S' : Finset (Fin n)) :
    ∃ RM : Finset (Finset (Fin n)),
      rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ RM ∧
      rc33_admOneSidedA n 𝒜 ℬ S' = rc37_admLeft n 𝒜 S' ∩ RM :=
  ⟨rc37_rightMem n ℬ, rc37_admOneSidedA_eq_inter n 𝒜 ℬ S, rc37_admOneSidedA_eq_inter n 𝒜 ℬ S'⟩


end StatMech.Walls
