/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part2


namespace StatMech.Universality

open Filter Set Topology

open Finset

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexBoundaryConsistencyError
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) : Real :=
  isingFiniteWeightedBoundaryError (vertexDirichletBoundary n)
    (vertexGhostPrimitive n hn) target

noncomputable def vertexTargetResidual
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) : Real :=
  isingFiniteWeightedTargetResidual (vertexGhostConductance n)
    (vertexDirichletBoundary n) target

noncomputable def vertexPoissonBarrierBound (n : Nat) : Real :=
  isingFiniteWeightedPoissonBarrierBound
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)

noncomputable def vertexTargetConsistencyError
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) : Real :=
  vertexBoundaryConsistencyError n hn target +
    vertexTargetResidual n target * vertexPoissonBarrierBound n

noncomputable def faceBoundaryConsistencyError
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) : Real :=
  isingFiniteWeightedBoundaryError (faceDirichletBoundary n)
    (faceGhostPrimitive n hn) target

noncomputable def faceTargetResidual
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) : Real :=
  isingFiniteWeightedTargetResidual (faceGhostConductance n)
    (faceDirichletBoundary n) target

noncomputable def facePoissonBarrierBound (n : Nat) : Real :=
  isingFiniteWeightedPoissonBarrierBound
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)

noncomputable def faceTargetConsistencyError
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) : Real :=
  faceBoundaryConsistencyError n hn target +
    faceTargetResidual n target * facePoissonBarrierBound n

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
