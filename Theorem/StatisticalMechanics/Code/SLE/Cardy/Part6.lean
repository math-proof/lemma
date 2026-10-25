/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Def.StatisticalMechanics.Code.SLE.Cardy.Part6
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

lemma kappaPercolation_selfTouching : IsSelfTouchingPhase kappaPercolation := by
  constructor <;> norm_num [kappaPercolation]


lemma kappaIsing_simple : IsSimplePhase kappaIsing := by
  constructor <;> norm_num [kappaIsing]


lemma kappaFKIsing_selfTouching : IsSelfTouchingPhase kappaFKIsing := by
  constructor <;> norm_num [kappaFKIsing]


@[simp] lemma centralCharge_percolation : centralCharge kappaPercolation = 0 := by
  norm_num [centralCharge, kappaPercolation]


@[simp] lemma centralCharge_ising : centralCharge kappaIsing = 1 / 2 := by
  norm_num [centralCharge, kappaIsing]


end StatMech.SLE
