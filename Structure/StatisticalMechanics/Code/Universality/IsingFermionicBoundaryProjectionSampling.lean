/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointClampedTarget.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalBoundaryProjectionSampling
    (N : Nat -> Nat) (mesh : Nat -> Real) (Phi : Complex -> Complex) where
  lipschitzConstant : NNReal
  imPhi_lipschitz : LipschitzWith lipschitzConstant (fun z => (Phi z).im)
  vertexProjection : forall k,
    {x : FKIsingSquareFullVertexNode (N k) //
      fkIsingSquareFullVertexFixedBoundary (N k) x} -> Complex
  faceProjection : forall k,
    {c : FKIsingSquareFullFaceNode (N k) //
      fkIsingSquareFullFaceFixedBoundary (N k) c} -> Complex
  vertexProjection_trace : forall k x, (Phi (vertexProjection k x)).im = 0
  faceProjection_trace : forall k c, (Phi (faceProjection k c)).im = 1
  vertexProjection_dist_le_mesh : forall k x,
    dist (fullSquareScaledVertexEmbedding (N k) (mesh k) x.1)
      (vertexProjection k x) <= mesh k
  faceProjection_dist_le_mesh : forall k c,
    dist (fullSquareScaledFaceEmbedding (N k) (mesh k) c.1)
      (faceProjection k c) <= mesh k


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
