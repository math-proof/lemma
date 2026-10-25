/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc7core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section EventCompression

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc7_flip (i : α) (ω : ConfigSpace α) : ConfigSpace α :=
  fun a => if a = i then !ω a else ω a

end EventCompression
end StatMech.Walls
