/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCalibratedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexCalibratedRobinEmbedding
    (n : Nat) (hn : 0 < n) (scale : Real)
    (x : FKIsingSquareFullVertexNode n) : Complex :=
  ⟨(fullSquareScaledVertexEmbedding n scale x).re,
    vertexDirichlet n hn (some x)⟩


noncomputable def faceCalibratedRobinEmbedding
    (n : Nat) (hn : 0 < n) (scale : Real)
    (c : FKIsingSquareFullFaceNode n) : Complex :=
  ⟨(fullSquareScaledFaceEmbedding n scale c).re,
    faceDirichlet n hn (some c)⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
