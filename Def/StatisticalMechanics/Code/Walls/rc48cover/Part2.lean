/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc48_C₁ : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {2}}


def rc48_D₁ : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {0, 1, 2}}


def rc48_A₂ : Finset (Finset (Fin 3)) := {∅, {0}}


def rc48_B₂ : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {1, 2}}


def rc48_E₂ : Finset (Finset (Fin 3)) := {{0}, {1}, {2}, {1, 2}}

end StatMech.Walls
