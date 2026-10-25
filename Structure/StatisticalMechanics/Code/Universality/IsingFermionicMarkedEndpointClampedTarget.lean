/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectedPrimitiveConvergence
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointClampedTarget.Part2


namespace StatMech.Universality

open Filter

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalEndpointLocalizedMarkedClampedRobinInputs
    (N : Nat -> Nat) (hN : forall k, 0 < N k)
    (Phi : Complex -> Complex) (mesh : Nat -> Real) (radius : Nat -> Nat)
    (boundaryRate bulkRate layerRate endpointRate : Nat -> Real) where
  boundary_nonneg : forall k, 0 <= boundaryRate k
  bulk_nonneg : forall k, 0 <= bulkRate k
  layer_nonneg : forall k, 0 <= layerRate k
  endpoint_nonneg : forall k, 0 <= endpointRate k
  vertexTrace : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      |0 - (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) x)).im| <= boundaryRate k
  faceTrace : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      |1 - (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) c)).im| <= boundaryRate k
  vertexBulk : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= bulkRate k
  faceBulk : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= bulkRate k
  vertexLayer : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= layerRate k
  faceLayer : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= layerRate k
  vertexEndpoint : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    vertexMarkedEndpointLayer (N k) (radius k) (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= endpointRate k
  faceEndpoint : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    faceMarkedEndpointLayer (N k) (radius k) (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= endpointRate k
  boundary_tendsto : Tendsto boundaryRate atTop (nhds 0)
  scaledBulk_tendsto : Tendsto
    (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0)
  layer_tendsto : Tendsto layerRate atTop (nhds 0)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
