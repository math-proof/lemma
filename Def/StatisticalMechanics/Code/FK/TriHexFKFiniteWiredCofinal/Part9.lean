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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part9
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarFiniteStarRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex n))) :=
  finiteRootBoundaryEvent (triHexPlanarFiniteStarGraph n)
    (triHexPlanarFiniteStarBoundary n) (triHexPlanarFiniteStarRoot n)

def triHexPlanarHexWhiteBufferedRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex (n + 1)))) :=
  finiteRootBoundaryEvent (hexagonal.bufferedGraph (n + 1))
    (hexagonal.bufferedBoundary (n + 1))
    (triHexPlanarHexWhiteBufferedRoot n)

end
end StatMech.FK.PeriodicPlanar
