/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part3


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexPointPoissonBarrier
    (n : Nat) (source : Option (FKIsingSquareFullVertexNode n)) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteWeightedPointPoissonBarrier
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) source


noncomputable def facePointPoissonBarrier
    (n : Nat) (source : Option (FKIsingSquareFullFaceNode n)) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteWeightedPointPoissonBarrier
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) source


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
