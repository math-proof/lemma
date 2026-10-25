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
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSCoordPath : HexAWCoord → Fin 6 → List ℤ → List HexAWCoord
  | c, h, [] => [c, hexAWNeighbor c (hexCSEdgeOfHeading c h)]
  | c, h, t :: ts =>
      c :: hexCSCoordPath
        (hexAWNeighbor c (hexCSEdgeOfHeading c h))
        (hexHeadingTurn h t) ts

end
end StatMech.Universality
