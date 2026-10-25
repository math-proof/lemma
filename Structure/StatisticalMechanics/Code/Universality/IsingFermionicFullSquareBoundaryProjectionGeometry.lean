/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure FullSquareOrdinaryBoundaryProjectionTraceData
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
      fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ region k /\
      (Phi (fullSquareVertexBoundaryProjection
        (N k) (mesh k) x)).im = 0
  faceFixed : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ region k /\
      fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c ∈ region k /\
      (Phi (fullSquareFaceFixedBoundaryProjection
        (N k) (mesh k) c)).im = 1
  vertexFree : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ region k /\
      (Phi (fullSquareVertexFreeBoundaryProjection
        (N k) (mesh k) x)).im = 1
  faceFree : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ region k /\
      fullSquareFaceFreeBoundaryProjection (N k) (mesh k) c ∈ region k /\
      (Phi (fullSquareFaceFreeBoundaryProjection
        (N k) (mesh k) c)).im = 0


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
