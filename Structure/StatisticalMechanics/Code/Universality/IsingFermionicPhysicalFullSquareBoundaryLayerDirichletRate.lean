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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure FullSquareCoordinateEmbeddingCompatibility
    (N : Nat → Nat)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (mesh : Nat → Real) where
  coordinateEmbedding : Nat → Int × Int → Complex
  vertex_eq_coordinate : ∀ k x,
    vertexEmbedding k x =
      coordinateEmbedding k (fkIsingSquareFullVertexCoordinate (N k) x)
  face_eq_coordinate : ∀ k c,
    faceEmbedding k c =
      coordinateEmbedding k (fkIsingSquareFullFaceCoordinate (N k) c)
  unitAxial_dist_le_mesh : ∀ k u v,
    (v = (u.1 + 1, u.2) ∨
      v = (u.1, u.2 + 1) ∨
      v = (u.1 - 1, u.2) ∨
      v = (u.1, u.2 - 1)) →
    dist (coordinateEmbedding k v) (coordinateEmbedding k u) ≤ mesh k


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
