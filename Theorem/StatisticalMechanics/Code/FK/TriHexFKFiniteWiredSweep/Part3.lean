/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part5
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem hexagonalGraph_adj_triHexPlanarCellTerminal
    (z : Site 2) (i : Fin 3) :
    hexagonalGraph.Adj (z, false) (triHexPlanarCellTerminal z i, true) := by
  simpa [triHexPlanarCellTerminal, hexagonalNeighbor] using
    hexagonal_adj_neighbor (z, false) i


theorem triangularGraph_adj_triHexPlanarCellTerminal
    (z : Site 2) (i j : Fin 3) (hij : i ≠ j) :
    triangularGraph.Adj (triHexPlanarCellTerminal z i)
      (triHexPlanarCellTerminal z j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [triHexPlanarCellTerminal, triangularGraph_adj, triangularAdj,
      hexagonalStep, triangularStep, funext_iff] <;> decide


theorem triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous
    (n : Nat) {q p : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio q p =
      (triHexPlanarFiniteWiredLevel n).triangleBoundaryReachRatio q p :=
  (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio_eq_triangle
    hq hp hsurface


theorem triHexPlanarFiniteWiredBoundaryReach_tendsto_iff_homogeneous
    {q p theta : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    Filter.Tendsto (fun n =>
        (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio q p)
        Filter.atTop (nhds theta) ↔
      Filter.Tendsto (fun n =>
        (triHexPlanarFiniteWiredLevel n).triangleBoundaryReachRatio q p)
        Filter.atTop (nhds theta) :=
  triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous
    triHexPlanarFiniteWiredLevel hq hp hsurface

end
end StatMech.FK.PeriodicPlanar
