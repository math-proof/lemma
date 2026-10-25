/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison


namespace StatMech.Universality

open Filter Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def faceSpatialTargetResidual
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    Option (FKIsingSquareFullFaceNode n) -> Real := by
  classical
  exact fun z =>
    if faceDirichletBoundary n z then 0 else
      |isingFiniteWeightedLaplacian (faceGhostConductance n) target z|


noncomputable def faceSpatialTargetResidualPotential
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteWeightedSpatialResidualPotential
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceSpatialTargetResidual n target)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
