/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk


namespace StatMech.Universality

open Filter

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalEndpointVariableLayerIncrementData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  constant : Nat -> NNReal
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
    forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
      |(Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
          constant k * mesh k
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
    forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
          constant k * mesh k


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
