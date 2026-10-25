/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRangeBound
import Mathlib.Analysis.Calculus.MeanValue
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly


namespace StatMech.Universality

open Filter Set Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointLayerIncrementData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <= 4 * H.constant * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullVertexGraph (N k))
    (fun y => (Phi (fullSquareScaledVertexEmbedding
      (N k) (mesh k) y)).im) x (H.constant * mesh k)
    (mul_nonneg H.constant.2 (hmesh k))
    (fullVertex_neighbor_card_le_four (N k) x)
    (H.vertex k x hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound

theorem PhysicalEndpointLayerIncrementData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <= 4 * H.constant * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullFaceGraph (N k))
    (fun d => (Phi (fullSquareScaledFaceEmbedding
      (N k) (mesh k) d)).im) c (H.constant * mesh k)
    (mul_nonneg H.constant.2 (hmesh k))
    (fullFace_neighbor_card_le_four (N k) c)
    (H.face k c hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound


theorem PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderLayerAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexFixed : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
    (hfaceFixed : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
    (hvertexFree : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
    (hfaceFree : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2)
      atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => 4 * Hlayer.constant * mesh k) (fun _ => 4) := by
  apply PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderAndRange
    (fun k => 4 * Hlayer.constant * mesh k) Hfourth hmesh_nonneg
  · intro k
    exact mul_nonneg (mul_nonneg (by norm_num) Hlayer.constant.2)
      (hmesh_nonneg k)
  · exact hvertexFixed
  · exact hfaceFixed
  · exact hvertexFree
  · exact hfaceFree
  · exact Hlayer.vertexLaplacian hmesh_nonneg
  · exact Hlayer.faceLaplacian hmesh_nonneg
  · exact hvertexRange
  · exact hfaceRange
  · exact hscaledFourth_tendsto
  · simpa using tendsto_const_nhds.mul hmesh_tendsto
  · exact hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
