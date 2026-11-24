module
public import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
public import Theorem.StatisticalMechanics.Code.Walls.rc2_hallavailable
public import Mathlib.Combinatorics.Hall.Basic
public import Theorem.StatisticalMechanics.Code.Walls.rc6hallavailable
open Finset Function
open scoped StatMech


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc6_fullRel (A B : Set (ConfigSpace α)) :
    ↥(rc6_boxFinset A B) → ↥(rc6_imgFinset A B) → Prop := fun _ _ => True

end StatMech.Walls
