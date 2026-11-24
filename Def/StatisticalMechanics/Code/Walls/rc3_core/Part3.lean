module
public import Theorem.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc3_slabimgeqinter.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc3_doubledboxcount.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc3_hallforswapinjection
public import Theorem.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
public import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
public import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
public import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def ReimerSubcubeReduction : Prop := ReimerCardFormAll → rc3_PerKeyAll


end StatMech.Walls
