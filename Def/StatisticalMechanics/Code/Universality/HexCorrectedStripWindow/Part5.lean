/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part4


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSBrickRadius (T L : ℕ) : ℕ := 4 * (T + L + 2)

end
end StatMech.Universality
