/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc35hallproof.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc36_A3ex : Finset (Finset (Fin 3)) := {∅, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}}


def rc36_B3ex : Finset (Finset (Fin 3)) := {∅, {0}, {1}}

end StatMech.Walls
