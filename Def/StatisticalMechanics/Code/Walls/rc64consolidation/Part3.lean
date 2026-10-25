/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc63doubledinjection.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc64consolidation.Part2
set_option linter.style.longLine false


set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc64_A3ex2 : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}}


def rc64_B3ex2 : Finset (Finset (Fin 3)) := {{0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

end StatMech.Walls
