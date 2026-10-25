/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc14reimerinduct
import Theorem.StatisticalMechanics.Code.Walls.rc15dimreduce.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc15_BKRground (E : Finset α) : Prop :=
  ∀ 𝒜 ℬ : Finset (Finset α), rc15_UpperOn E 𝒜 → rc15_UpperOn E ℬ →
    #(rc14_boxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)


def rc15_SliceUnionBound : Prop :=
  ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
    rc15_UpperOn E 𝒜 → rc15_UpperOn E ℬ →
      #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
          ∪ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))


end StatMech.Walls
