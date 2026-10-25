/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Def.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport.Part3
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem triangularTorusRadialPercolates_iff_hexagonal
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    TriangularTorusRadialPercolates p q ↔
      HexagonalTorusRadialPercolates p q := by
  have heq : hexagonalTorusRadialReachProbability p q =
      triangularTorusRadialReachProbability p q := by
    funext n
    exact triHexFK_torus_radialReachProbability_eq hq hp hsurface n
  simp only [TriangularTorusRadialPercolates,
    HexagonalTorusRadialPercolates, heq]


end
end StatMech.FK.PeriodicPlanar
