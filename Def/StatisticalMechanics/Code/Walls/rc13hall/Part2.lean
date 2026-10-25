/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc13hall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc13_MarriageCondition (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∀ 𝒯 ⊆ rc10_boxSupp 𝒜 ℬ, #𝒯 ≤ #(𝒯.biUnion (rc13_adm 𝒜 ℬ))


end StatMech.Walls
