/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc59doubledcover.Part5
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc60_A3ex : Finset (Finset (Fin 3)) := {∅, {0}, {2}}


def rc60_B3ex : Finset (Finset (Fin 3)) := {{0}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

end StatMech.Walls
