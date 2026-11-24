module
public import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
public import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
public import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
public import Theorem.StatisticalMechanics.Code.Walls.rc39famcyl
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def dc39_A : Finset (Finset (Fin 3)) := {{2}, {1, 2}, {0, 1, 2}}

def dc39_B : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

def dc39_C : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

def dc39_D : Finset (Finset (Fin 3)) := {∅, {1}, {0, 1}}

def dc39_E : Finset (Finset (Fin 3)) := {{0, 1}}

def dc39_F : Finset (Finset (Fin 3)) := {{0, 2}}


end StatMech.Walls
