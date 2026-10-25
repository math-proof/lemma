/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicAnalyticFourthOrder
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalFourthOrder.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2


namespace StatMech.Universality

open Filter Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointFourthOrderBulkData.ofAnalyticTensorNorm
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (M : NNReal)
    (hsmooth : ContDiff Real 4 (fun w => (Phi w).im))
    (htensor : forall w,
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        AnalyticAt Complex Phi
          (fullSquareScaledVertexEmbedding (N k) (mesh k) x))
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        AnalyticAt Complex Phi
          (fullSquareScaledFaceEmbedding (N k) (mesh k) c)) :
    PhysicalEndpointFourthOrderBulkData N Phi mesh radius where
  boundOne := 4 * M
  boundTwo := 4 * M
  boundSum_nonneg := by positivity
  vertex k x hfixed hghost hendpoint :=
    DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm
      Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x) M
      hsmooth htensor (hvertex k x hfixed hghost hendpoint)
  face k c hfixed hghost hendpoint :=
    DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm
      Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c) M
      hsmooth htensor (hface k c hfixed hghost hendpoint)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
