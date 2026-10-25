/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc14reimerinduct
import Theorem.StatisticalMechanics.Code.Walls.rc15dimreduce
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc15_UpperOn (E : Finset α) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ⊆ T → T ⊆ E → S ∈ 𝒜 → T ∈ 𝒜

end StatMech.Walls
