/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc13hall.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc13_marriageSearch (𝒜 ℬ : Finset (Finset (Fin 2))) : Bool :=
  decide (∀ 𝒯 ∈ (rc12_boxSuppComp 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc13_admComp 𝒜 ℬ)).card)

end StatMech.Walls
