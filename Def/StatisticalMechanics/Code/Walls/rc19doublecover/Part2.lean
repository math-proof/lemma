/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc19_DoubledReflection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ f : Finset α → Finset α,
    Set.InjOn f (rc18_cylBoxSupp A B : Set (Finset α)) ∧
    ∀ S ∈ rc18_cylBoxSupp A B, f S ∈ rc10_reflInter (eventFamily A) (eventFamily B)

end StatMech.Walls
