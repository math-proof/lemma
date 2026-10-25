/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11bkriffincinc
import Theorem.StatisticalMechanics.Code.Walls.rc11boxsuppupper
import Theorem.StatisticalMechanics.Code.Walls.rc11reflinterstructure
import Theorem.StatisticalMechanics.Code.Walls.rc11doublecoverrepresentation
import Theorem.StatisticalMechanics.Code.Walls.rc11compressionengine
import Theorem.StatisticalMechanics.Code.Walls.rc11core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc11_BKRInjection (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∃ f : Finset α → Finset α, Set.InjOn f (rc10_boxSupp 𝒜 ℬ) ∧
    ∀ S ∈ rc10_boxSupp 𝒜 ℬ, f S ∈ rc10_reflInter 𝒜 ℬ

end StatMech.Walls
