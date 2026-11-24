module
public import Theorem.StatisticalMechanics.Code.Walls.rc54weighted.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
public import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Theorem.StatisticalMechanics.Code.Walls.rc55nonproduct
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


def rc55_leftProj (U : Finset (α ⊕ α)) : Finset α :=
  univ.filter (fun a => Sum.inl a ∈ U)


def rc55_rightProj (U : Finset (α ⊕ α)) : Finset α :=
  univ.filter (fun a => Sum.inr a ∈ U)


def rc55_isSuperfill (U : Finset (α ⊕ α)) : Prop :=
  rc55_leftProj U ∪ rc55_rightProj U = univ

end StatMech.Walls
