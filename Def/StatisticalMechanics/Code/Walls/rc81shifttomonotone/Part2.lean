/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc81shifttomonotone
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc81_upClosure (A : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  Finset.univ.filter (fun w => ∃ a ∈ A, rc81_le a w = true)


def rc81_downClosure (B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  Finset.univ.filter (fun w => ∃ b ∈ B, rc81_le w b = true)

end StatMech.Walls
