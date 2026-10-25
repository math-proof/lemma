/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFiniteDualComparison
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part17
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

def triHexPlanarFiniteStarExtendEdge (m : Nat)
    (omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V)) :
    ConfigSpace (Sym2 HexVertex) := fun e =>
  if h : e ∈ Set.range (triHexPlanarFiniteStarEdgeIncl m) then
    omega h.choose
  else false

end
end StatMech.FK.PeriodicPlanar
