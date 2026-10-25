/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part2


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def fullSquareScaledEmbeddingCompatibility
    (N : Nat → Nat) (mesh : Nat → Real)
    (hmesh : ∀ k, 0 ≤ mesh k) :
    FullSquareCoordinateEmbeddingCompatibility N
      (fun k ↦ fullSquareScaledVertexEmbedding (N k) (mesh k))
      (fun k ↦ fullSquareScaledFaceEmbedding (N k) (mesh k)) mesh where
  coordinateEmbedding k := fullSquareScaledCoordinateEmbedding (mesh k)
  vertex_eq_coordinate _ _ := rfl
  face_eq_coordinate _ _ := rfl
  unitAxial_dist_le_mesh k u v hunit :=
    fullSquareScaledCoordinateEmbedding_unitAxial_dist
      (mesh k) (hmesh k) u v hunit

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
