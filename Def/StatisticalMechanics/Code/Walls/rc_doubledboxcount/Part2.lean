/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Walls.rc_doubledboxcount
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


def collapseFamily : Finset (Finset (Fin 2)) := {∅, {1}}


end StatMech.Walls
