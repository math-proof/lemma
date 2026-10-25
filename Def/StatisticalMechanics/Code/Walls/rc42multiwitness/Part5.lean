/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc42_hallCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ 𝒯 ∈ (rc21_boxComp n 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc42_admCoveringComp n 𝒜 ℬ)).card)

end StatMech.Walls
