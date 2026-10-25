/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6relabelinvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Theorem.StatisticalMechanics.Code.Walls.rc6relabelinvariance
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace


def rc6_DeficitNonposAllFinite : Prop :=
  ∀ (β : Type) [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)), rc6_deficit A B ≤ 0


end StatMech.Walls
