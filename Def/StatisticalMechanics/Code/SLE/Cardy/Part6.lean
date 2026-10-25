/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part5
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

def kappaPercolation : ℝ := 6


def kappaIsing : ℝ := 3


noncomputable def kappaFKIsing : ℝ := 16 / 3


noncomputable def centralCharge (κ : ℝ) : ℝ := (3 * κ - 8) * (6 - κ) / (2 * κ)


end StatMech.SLE
