/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc12_isUpperFin (n : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ S ∈ 𝒜, ∀ T : Finset (Fin n), S ⊆ T → T ∈ 𝒜

end StatMech.Walls
