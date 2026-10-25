/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc40_Aref : Finset (Finset (Fin 3)) := {∅, {0}, {1}}


def rc40_Bref : Finset (Finset (Fin 3)) := {{0}, {0, 1}, {0, 1, 2}, {0, 2}, {1}, {1, 2}}

end StatMech.Walls
