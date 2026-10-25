/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc44boxineq.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc45doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc45_Astep : Finset (Finset (Fin 3)) := {{0}, {0, 2}, {1, 2}}


def rc45_Bstep : Finset (Finset (Fin 3)) := {{0, 1, 2}, {0, 2}, {1, 2}, {2}}


end StatMech.Walls
