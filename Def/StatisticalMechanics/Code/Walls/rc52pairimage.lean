/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc52pairimage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc51refute.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc52_pairImage (S K L : Finset α) : Finset α × Finset α :=
  (rc49_jointImage S K L, (rc49_jointImage S K L)ᶜ)


end StatMech.Walls
