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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2


namespace StatMech.Universality

open Filter Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticTensorNormOnSegments
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U : Set Complex) (hU : IsOpen U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) U)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) U ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) U) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius where
  boundOne := 4 * (M : Real)
  boundTwo := 4 * (M : Real)
  boundSum_nonneg := by positivity
  vertex k x hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      U hU hPhi M htensor hpositiveOne hnegativeOne
        hpositiveTwo hnegativeTwo
  face k c hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      U hU hPhi M htensor hpositiveOne hnegativeOne
        hpositiveTwo hnegativeTwo


noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactSegments
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) K ∧
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) K) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  let hex :=
    exists_iteratedFDeriv_norm_bound_on_compact Phi U K hU hK hKU hPhi
  let M : NNReal := Classical.choose hex
  have hM : forall w, w ∈ K ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M :=
    Classical.choose_spec hex
  exact {
    boundOne := 4 * (M : Real)
    boundTwo := 4 * (M : Real)
    boundSum_nonneg := by positivity
    vertex := fun k x hfixed hghost hendpoint => by
      obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
        hvertex k x hfixed hghost hendpoint
      exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments
        U K hU hKU hPhi M hM hpositiveOne hnegativeOne
          hpositiveTwo hnegativeTwo
    face := fun k c hfixed hghost hendpoint => by
      obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
        hface k c hfixed hghost hendpoint
      exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments
        U K hU hKU hPhi M hM hpositiveOne hnegativeOne
          hpositiveTwo hnegativeTwo }


noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactConvex
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hKConvex : Convex Real K) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      z ∈ K ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ K ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      z ∈ K ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ K ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ K ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ K) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  apply PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactSegments
    U K hU hK hKU hPhi
  · intro k x hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeTwo⟩
  · intro k c hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex K hKConvex _ _ _ hz hnegativeTwo⟩


noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticTensorNormOnConvex
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U : Set Complex) (hUOpen : IsOpen U) (hUConvex : Convex Real U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      z ∈ U ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ U ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ U)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      z ∈ U ∧
        z + (mesh k : Complex) * (1 + Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 + Complex.I) ∈ U ∧
        z + (mesh k : Complex) * (1 - Complex.I) ∈ U ∧
        z + ((-mesh k : Real) : Complex) * (1 - Complex.I) ∈ U) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  apply PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticTensorNormOnSegments
    U hUOpen hPhi M htensor
  · intro k x hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeTwo⟩
  · intro k c hfixed hghost hendpoint
    obtain ⟨hz, hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact ⟨
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeOne,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hpositiveTwo,
      complexLine_mapsTo_uIcc_of_convex U hUConvex _ _ _ hz hnegativeTwo⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
