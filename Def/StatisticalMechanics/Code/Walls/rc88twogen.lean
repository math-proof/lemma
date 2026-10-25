/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc87extra.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc88twogen
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 800000

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc88_a3 : ConfigSpace (Fin 3) := ![false, true, false]

def rc88_b3 : ConfigSpace (Fin 3) := ![true, true, false]


def rc88_A3 : Finset (ConfigSpace (Fin 3)) := {rc88_a3, rc88_b3}


end StatMech.Walls
