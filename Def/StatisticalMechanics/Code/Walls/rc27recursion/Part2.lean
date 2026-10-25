/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc26cubefill
import Theorem.StatisticalMechanics.Code.Walls.rc27recursion
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc27_BoxSuppRecursion : Prop :=
  ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
    #(rc14_boxE E 𝒜 ℬ)
      ≤ #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))

end StatMech.Walls
