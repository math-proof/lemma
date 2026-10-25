/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Mathlib.Combinatorics.Hall.Basic
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc58_Amono : Finset (Finset (Fin 2)) := {∅, {0}, {1}}


def rc58_Bmono : Finset (Finset (Fin 2)) := {∅, {0}, {0, 1}}

end StatMech.Walls
