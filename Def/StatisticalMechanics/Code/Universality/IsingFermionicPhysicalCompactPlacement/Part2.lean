/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part2


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointLayerIncrementData.ofLipschitzOnCompactCenters
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S K : Set Complex) (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S)
    (epsilon : Real) (hcollar : Metric.cthickening epsilon K ⊆ S)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hmesh_collar : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius := by
  have hepsilon : 0 ≤ epsilon :=
    (mul_nonneg (by norm_num) (abs_nonneg (mesh 0))).trans
      (hmesh_collar 0)
  apply PhysicalEndpointLayerIncrementData.ofLipschitzOn
    S L hPhi hmesh_nonneg
  · intro k x hfixed hghost hendpoint
    have hx := hvertex k x hfixed hghost hendpoint
    constructor
    · exact hcollar (Metric.mem_cthickening_of_dist_le _ _ epsilon K hx
        (by simpa using hepsilon))
    · intro y hxy
      apply hcollar
      apply Metric.mem_cthickening_of_dist_le _
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x) epsilon K hx
      exact (fullSquareScaledVertexEmbedding_dist_le_two_abs
        (N k) (mesh k) x y hxy).trans (hmesh_collar k)
  · intro k c hfixed hghost hendpoint
    have hc := hface k c hfixed hghost hendpoint
    constructor
    · exact hcollar (Metric.mem_cthickening_of_dist_le _ _ epsilon K hc
        (by simpa using hepsilon))
    · intro d hcd
      apply hcollar
      apply Metric.mem_cthickening_of_dist_le _
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c) epsilon K hc
      exact (fullSquareScaledFaceEmbedding_dist_le_two_abs
        (N k) (mesh k) c d hcd).trans (hmesh_collar k)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
