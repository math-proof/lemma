module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
public import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


def rc5_collapseFamily : Finset (Finset (Fin 2)) := {∅, {1}}


end StatMech.Walls
