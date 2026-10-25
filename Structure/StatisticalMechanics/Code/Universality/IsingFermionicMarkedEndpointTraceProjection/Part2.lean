/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalEndpointOrdinaryBoundaryProjectionData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  lipschitzConstant : Nat -> NNReal
  region : Nat -> Set Complex
  imPhi_lipschitz : forall k,
    LipschitzOnWith (lipschitzConstant k)
      (fun z => (Phi z).im) (region k)
  vertexFixed : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x) 0 (mesh k)
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c) 1 (mesh k)
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x) 1 (mesh k)
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      LocalBoundaryTraceProjection Phi (region k) (lipschitzConstant k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c) 0 (mesh k)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
