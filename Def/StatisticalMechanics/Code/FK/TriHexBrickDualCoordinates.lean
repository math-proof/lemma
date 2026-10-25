/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFiniteDualComparison
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part17
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

def triHexPlanarFiniteStarEdgeIncl (m : Nat) :
    Sym2 (triHexPlanarFiniteStarPlanar m).V → Sym2 HexVertex :=
  Sym2.map (triHexPlanarFiniteStarVertexEmbedding m)

end
end StatMech.FK.PeriodicPlanar
