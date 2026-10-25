/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRangeBound
import Mathlib.Analysis.Calculus.MeanValue
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly


namespace StatMech.Universality

open Filter Set Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointFourthOrderBulkData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <=
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.vertex k x hfixed hghost hendpoint
  exact fullSquareScaledVertex_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z => (Phi z).im) x
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic

theorem PhysicalEndpointFourthOrderBulkData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <=
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.face k c hfixed hghost hendpoint
  exact fullSquareScaledFace_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z => (Phi z).im) c
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic


theorem PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat} (layerRate : Nat -> Real)
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hlayer_nonneg : forall k, 0 <= layerRate k)
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
    (hvertexLayer : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
          (fun y => (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| <= layerRate k)
    (hfaceLayer : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
          (fun d => (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| <= layerRate k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2)
      atTop (nhds 0))
    (hlayer_tendsto : Tendsto layerRate atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      layerRate (fun _ => 4) := by
  refine
    { mesh_nonneg := hmesh_nonneg
      bulk_nonneg := ?_
      layer_nonneg := hlayer_nonneg
      endpoint_nonneg := fun _ => by norm_num
      vertexFixed := hvertexFixed
      faceFixed := hfaceFixed
      vertexFree := hvertexFree
      faceFree := hfaceFree
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := hvertexLayer
      faceLayer := hfaceLayer
      vertexEndpoint := ?_
      faceEndpoint := ?_
      scaledBulk_tendsto := ?_
      layer_tendsto := hlayer_tendsto
      mesh_tendsto := hmesh_tendsto }
  · intro k
    exact div_nonneg
      (mul_nonneg Hfourth.boundSum_nonneg (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · exact fun k x hfixed hghost hendpoint =>
      Hfourth.vertexLaplacian k x hfixed hghost hendpoint
  · exact fun k c hfixed hghost hendpoint =>
      Hfourth.faceLaplacian k c hfixed hghost hendpoint
  · intro k x _hfixed _hendpoint
    exact fullSquareVertex_sampledLaplacian_le_four_of_unitRange
      (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k))
      Phi (hvertexRange k) x
  · intro k c _hfixed _hendpoint
    exact fullSquareFace_sampledLaplacian_le_four_of_unitRange
      (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k))
      Phi (hfaceRange k) c
  · have hconstant : Tendsto
        (fun _ : Nat => (Hfourth.boundOne + Hfourth.boundTwo) / 12)
        atTop (nhds ((Hfourth.boundOne + Hfourth.boundTwo) / 12)) :=
      tendsto_const_nhds
    have hproduct := hconstant.mul hscaledFourth_tendsto
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hproduct


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
