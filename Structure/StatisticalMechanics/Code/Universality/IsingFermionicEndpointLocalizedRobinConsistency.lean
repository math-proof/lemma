/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part3


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalEndpointLocalizedRobinInputs
    (N : Nat -> Nat) (hN : forall k, 0 < N k)
    (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat)
    (bulkRate layerRate endpointRate : Nat -> Real) where
  mesh_nonneg : forall k, 0 <= mesh k
  bulk_nonneg : forall k, 0 <= bulkRate k
  layer_nonneg : forall k, 0 <= layerRate k
  endpoint_nonneg : forall k, 0 <= endpointRate k
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0
  vertexBulk : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= bulkRate k
  faceBulk : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= bulkRate k
  vertexLayer : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= layerRate k
  faceLayer : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= layerRate k
  vertexEndpoint : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    vertexMarkedEndpointLayer (N k) (radius k) (some x) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| <= endpointRate k
  faceEndpoint : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    faceMarkedEndpointLayer (N k) (radius k) (some c) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| <= endpointRate k
  scaledBulk_tendsto : Tendsto
    (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0)
  layer_tendsto : Tendsto layerRate atTop (nhds 0)
  mesh_tendsto : Tendsto mesh atTop (nhds 0)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
