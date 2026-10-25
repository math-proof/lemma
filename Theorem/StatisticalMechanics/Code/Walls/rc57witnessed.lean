/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Mathlib.Combinatorics.Hall.Basic
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc57_witnessedInter_iff_injection (𝒜 ℬ : Finset (Finset α)) :
    #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) ↔
      Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset α))
        ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset α))) := by
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_coe, Fintype.card_coe]


end StatMech.Walls
