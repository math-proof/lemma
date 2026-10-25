/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc2_hallavailable
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc6hallavailable.Part2
open Finset Function
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


instance rc6_fullRel_decidable (A B : Set (ConfigSpace α)) :
    DecidableRel (rc6_fullRel A B) := fun _ _ => instDecidableTrue

end StatMech.Walls
