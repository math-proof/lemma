/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part7
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarHexWhiteRoot : HexVertex := (hexagonalStep 0, true)


def triHexPlanarFiniteStarRoot (n : Nat) :
    TriHexPlanarFiniteStarVertex n :=
  Sum.inr (triHexPlanarFiniteTerminalMap n
    (triHexPlanarFiniteRootCell n) 0)

end
end StatMech.FK.PeriodicPlanar
