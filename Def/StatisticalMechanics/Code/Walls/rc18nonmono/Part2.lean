/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc17arbitrary.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Theorem.StatisticalMechanics.Code.Walls.rmr_cylinderwitness
import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc18_CylBoxReflInter : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B))

end StatMech.Walls
