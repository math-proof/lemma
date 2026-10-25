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
import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc57_ReflMatching : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset (Fin n)))
      ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset (Fin n))))

end StatMech.Walls
