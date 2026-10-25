/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc45doubledcover.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Instance.StatisticalMechanics.Code.Walls.rc46butterfly
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc46_Acf : Finset (Finset (Fin 3)) := {∅, {1}}


def rc46_Bcf : Finset (Finset (Fin 3)) := {{0, 1, 2}, {0, 2}}


end StatMech.Walls
