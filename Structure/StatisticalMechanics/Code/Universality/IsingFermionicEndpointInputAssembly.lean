/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRangeBound
import Mathlib.Analysis.Calculus.MeanValue


namespace StatMech.Universality

open Filter Set Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalEndpointFourthOrderBulkData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) (radius : Nat -> Nat) where
  boundOne : Real
  boundTwo : Real
  boundSum_nonneg : 0 <= boundOne + boundTwo
  vertex : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      DirectionalFourthOrderHarmonicData (fun z => (Phi z).im)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
        boundOne boundTwo
  face : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      DirectionalFourthOrderHarmonicData (fun z => (Phi z).im)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
        boundOne boundTwo

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
