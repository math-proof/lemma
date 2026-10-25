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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part3
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq
    (n : Nat)
    (eta : ConfigSpace
      (triHexPlanarFiniteTriangleInducedGraph (n + 1)).edgeSet) :
    triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n + 1) eta =
      triHexPlanarFiniteTriangleBoundaryReachIndicator (n + 1)
        (activeGraphRestrict
          (triHexPlanarFiniteTriangleGraph (n + 1))
          (triHexPlanarFiniteTriangleInducedGraph (n + 1))
          (triHexPlanarFiniteTriangleGraph_le_induced (n + 1)) eta) := by
  unfold triHexPlanarFiniteTriangleInducedBoundaryReachIndicator
    triHexPlanarFiniteTriangleBoundaryReachIndicator
  congr 1
  apply propext
  exact boundaryReachable_iff_of_le_sup_boundaryClique
    (triHexPlanarFiniteTriangleGraph (n + 1))
    (triHexPlanarFiniteTriangleInducedGraph (n + 1))
    (triHexPlanarFiniteBoundary (n + 1))
    (triHexPlanarFiniteTriangleGraph_le_induced (n + 1))
    (by simpa [triHexPlanarFiniteTriangleInducedGraph] using
      triHexPlanarFiniteTriangle_induced_le_wiredGraph (n + 1))
    (triHexPlanarFiniteRoot_not_boundary_succ n) eta


end
end StatMech.FK.PeriodicPlanar
