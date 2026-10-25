/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc53butterfly.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc54weighted
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc54_wA : Finset (Finset (Fin 2)) := {∅, {0}}


def rc54_wB : Finset (Finset (Fin 2)) := {∅, {1}}


noncomputable def rc54_wWt : Fin 2 → Bool → ℝ := fun _ b => if b then (1 : ℝ) / 2 else 1


end StatMech.Walls
