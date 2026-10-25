/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc47_A₁ : Finset (Finset (Fin 3)) := {∅, {0}}


def rc47_B₁ : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {1, 2}}


def rc47_B₂ : Finset (Finset (Fin 3)) := {∅, {1}, {2}, {1, 2}}


def rc47_B₃ : Finset (Finset (Fin 3)) := {∅, {1}, {2}, {1, 2}, {0, 1, 2}}

end StatMech.Walls
