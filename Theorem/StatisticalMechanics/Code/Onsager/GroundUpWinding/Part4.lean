/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Def.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part3

public section

namespace StatMech.Onsager.GroundUp

theorem staircase_balance (k : ℕ) : staircaseModel.balance k = 4 :=
  staircaseModel.umlaufsatz k trivial


end StatMech.Onsager.GroundUp
