/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc81shifttomonotone.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc81_botF : ConfigSpace (Fin 2) := fun _ => false


def rc81_wA : Finset (ConfigSpace (Fin 2)) := {rc81_botF}


end StatMech.Walls
