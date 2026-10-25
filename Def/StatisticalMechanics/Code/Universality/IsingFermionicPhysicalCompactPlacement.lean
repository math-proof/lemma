/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactCenters
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (epsilon : Real)
    (hcollar : Metric.cthickening epsilon K ⊆ U)
    (hmesh : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K) :
    PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius := by
  apply PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactSegments
    U (Metric.cthickening epsilon K) hU hK.cthickening hcollar hPhi
  · intro k x hfixed hghost hendpoint
    let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
    have hz : z ∈ K := hvertex k x hfixed hghost hendpoint
    exact ⟨
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) false,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) false⟩
  · intro k c hfixed hghost hendpoint
    let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
    have hz : z ∈ K := hface k c hfixed hghost hendpoint
    exact ⟨
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) true,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (mesh k) (hmesh k) false,
      by simpa [z] using
        diagonalSegment_mapsTo_cthickening K epsilon z hz
          (-mesh k) (by simpa using hmesh k) false⟩


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
