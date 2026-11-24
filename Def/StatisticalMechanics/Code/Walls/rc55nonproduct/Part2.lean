module
public import Theorem.StatisticalMechanics.Code.Walls.rc54weighted.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
public import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Instance.StatisticalMechanics.Code.Walls.rc55nonproduct
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc55_superfillCount (F : Finset (Finset (α ⊕ α))) : ℕ :=
  (F.filter rc55_isSuperfill).card


end StatMech.Walls
