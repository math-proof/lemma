/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part3
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

def IsSimplePhase (κ : ℝ) : Prop := 0 ≤ κ ∧ κ ≤ 4


def IsSelfTouchingPhase (κ : ℝ) : Prop := 4 < κ ∧ κ < 8


def IsSpaceFillingPhase (κ : ℝ) : Prop := 8 ≤ κ


end StatMech.SLE
