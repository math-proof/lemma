/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part4


namespace StatMech.Universality

open Filter Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexSpatialTargetResidual
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    Option (FKIsingSquareFullVertexNode n) -> Real := by
  classical
  exact fun z =>
    if vertexDirichletBoundary n z then 0 else
      |isingFiniteWeightedLaplacian (vertexGhostConductance n) target z|


noncomputable def vertexSpatialTargetResidualPotential
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteWeightedSpatialResidualPotential
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
