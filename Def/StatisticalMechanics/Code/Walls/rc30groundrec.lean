/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc30groundrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc29reconcile.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc30groundrec
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc30_SameSideReflDom : Prop :=
  ∀ (F : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α),
    #(rc14_reflE F (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_reflE F (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
      ≤ #(rc14_reflE F (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE F (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))


end StatMech.Walls
