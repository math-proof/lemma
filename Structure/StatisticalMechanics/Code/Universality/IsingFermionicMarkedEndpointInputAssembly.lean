/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointInputAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointClampedTarget.Part3


namespace StatMech.Universality

open Filter

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalEndpointOrdinaryTraceData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat)
    (traceRate : Nat -> Real) where
  trace_nonneg : forall k, 0 <= traceRate k
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      |0 - (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) x)).im| <= traceRate k
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      |1 - (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) c)).im| <= traceRate k
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |1 - (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) x)).im| <= traceRate k
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |0 - (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) c)).im| <= traceRate k
  trace_tendsto : Tendsto traceRate atTop (nhds 0)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
