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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part4
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (n + 1) p q =
      triHexPlanarFiniteTriangleWiredBoundaryProbability (n + 1) p q := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability,
    ← activeBCMean_boundaryClique_eq_wired
      (triHexPlanarFiniteTriangleInducedGraph (n + 1))
      (triHexPlanarFiniteBoundary (n + 1)) hp hp1 hq]
  rw [triHexPlanarFiniteTriangleWiredBoundaryProbability,
    ← wiredActiveRatio_eq_wiredFkProb_lift
      (triHexPlanarFiniteTriangleGraph (n + 1))
      (triHexPlanarFiniteBoundary (n + 1)) hp hp1 hq]
  rw [show triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n + 1) =
      fun eta => triHexPlanarFiniteTriangleBoundaryReachIndicator (n + 1)
        (activeGraphRestrict
          (triHexPlanarFiniteTriangleGraph (n + 1))
          (triHexPlanarFiniteTriangleInducedGraph (n + 1))
          (triHexPlanarFiniteTriangleGraph_le_induced (n + 1)) eta) by
    funext eta
    exact triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq n eta]
  rw [activeBCMean_eq_of_le_sup_boundaryClique
    (triHexPlanarFiniteTriangleGraph (n + 1))
    (triHexPlanarFiniteTriangleInducedGraph (n + 1))
    (triHexPlanarFiniteBoundary (n + 1))
    (triHexPlanarFiniteTriangleGraph_le_induced (n + 1))
    (by simpa [triHexPlanarFiniteTriangleInducedGraph] using
      triHexPlanarFiniteTriangle_induced_le_wiredGraph (n + 1))]
  rw [activeBCMean_eq_div]
  unfold wiredActiveRatio wiredActiveNumer wiredActiveZ wiredActiveWeight
    activeBCNumer activeBCZ activeBCWeight wiredFkWeight
  simp only [numClustersBC_boundaryClique]
  rfl


theorem triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous
    (n : Nat) {q p : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    triHexPlanarFiniteStarWiredBoundaryProbability (n + 1)
        (BeffaraDC.dualParam p q) q =
      triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (n + 1) p q := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq
    n hp.1 hp.2 hq]
  exact triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous
    (n + 1) hq hp hsurface


end
end StatMech.FK.PeriodicPlanar
