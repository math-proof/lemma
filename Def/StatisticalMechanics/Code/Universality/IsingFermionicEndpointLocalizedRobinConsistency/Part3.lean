/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part2


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexMarkedEndpointBarrier (n radius : Nat) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteWeightedLocalizedPoissonBarrier
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)


noncomputable def faceMarkedEndpointBarrier (n radius : Nat) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteWeightedLocalizedPoissonBarrier
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
