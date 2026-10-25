/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectedPrimitiveConvergence
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointClampedTarget


namespace StatMech.Universality

open Filter

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

@[simp] theorem vertexMarkedEndpointClampedSampledTarget_of_not_fixed
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    vertexMarkedEndpointClampedSampledTarget n embedding Phi (some x) =
      (Phi (embedding x)).im := by
  simp [vertexMarkedEndpointClampedSampledTarget, isingBoundaryClamp,
    vertexMarkedBoundaryEndpoint, hx, isingFiniteGhostExtension]

@[simp] theorem faceMarkedEndpointClampedSampledTarget_of_not_fixed
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    faceMarkedEndpointClampedSampledTarget n embedding Phi (some c) =
      (Phi (embedding c)).im := by
  simp [faceMarkedEndpointClampedSampledTarget, isingBoundaryClamp,
    faceMarkedBoundaryEndpoint, hc, isingFiniteGhostExtension]


theorem vertexMarkedEndpointClamped_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall x, fkIsingSquareFullVertexFixedBoundary n x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) ->
        |0 - (Phi (embedding x)).im| <= traceBound) :
    vertexBoundaryConsistencyError n hn
      (vertexMarkedEndpointClampedSampledTarget n embedding Phi) <=
        traceBound := by
  apply isingFiniteWeightedBoundaryError_le
    (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
    (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
    traceBound htrace_nonneg
  intro z hz
  cases z with
  | none =>
      simpa [vertexGhostPrimitive, vertexMarkedEndpointClampedSampledTarget,
        isingFiniteGhostExtension] using htrace_nonneg
  | some x =>
      change fkIsingSquareFullVertexFixedBoundary n x at hz
      by_cases hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x
      · simp [vertexGhostPrimitive, vertexMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          vertexMarkedBoundaryEndpoint, hz, hghost,
          vertex_fixedBoundary_eq_zero n hn x hz, htrace_nonneg]
      · simpa [vertexGhostPrimitive, vertexMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          vertexMarkedBoundaryEndpoint, hz, hghost,
          vertex_fixedBoundary_eq_zero n hn x hz] using htrace x hz hghost


theorem faceMarkedEndpointClamped_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall c, fkIsingSquareFullFaceFixedBoundary n c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) ->
        |1 - (Phi (embedding c)).im| <= traceBound) :
    faceBoundaryConsistencyError n hn
      (faceMarkedEndpointClampedSampledTarget n embedding Phi) <=
        traceBound := by
  apply isingFiniteWeightedBoundaryError_le
    (faceDirichletBoundary n) (faceGhostPrimitive n hn)
    (faceMarkedEndpointClampedSampledTarget n embedding Phi)
    traceBound htrace_nonneg
  intro z hz
  cases z with
  | none =>
      simpa [faceGhostPrimitive, faceMarkedEndpointClampedSampledTarget,
        isingFiniteGhostExtension] using htrace_nonneg
  | some c =>
      change fkIsingSquareFullFaceFixedBoundary n c at hz
      by_cases hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n c
      · simp [faceGhostPrimitive, faceMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          faceMarkedBoundaryEndpoint, hz, hghost,
          face_fixedBoundary_eq_one n hn c hz, htrace_nonneg]
      · simpa [faceGhostPrimitive, faceMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          faceMarkedBoundaryEndpoint, hz, hghost,
          face_fixedBoundary_eq_one n hn c hz] using htrace c hz hghost


theorem vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled
    (n radius : Nat) (hradius : 0 < radius)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hendpoint : Not (vertexMarkedEndpointLayer n radius (some x))) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x) =
      isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexSampledImaginaryTarget n embedding Phi) (some x) := by
  have hsampled : vertexSampledImaginaryTarget n embedding Phi =
      isingFiniteGhostExtension 1 (fun y => (Phi (embedding y)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold vertexGhostConductance vertexMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some, isingFiniteGhostLaplacian_some]
  have hxvalue : isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
      (fun y => (Phi (embedding y)).im) x = (Phi (embedding x)).im := by
    simp [isingBoundaryClamp, vertexMarkedBoundaryEndpoint, hx]
  have hlap := isingFiniteGraphLaplacian_eq_of_eq_on_neighbors
    (fkIsingSquareFullVertexGraph n)
    (isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
      (fun y => (Phi (embedding y)).im))
    (fun y => (Phi (embedding y)).im) x hxvalue
  rw [hlap]
  · rw [hxvalue]
  · intro y hxy
    have hnot : Not (vertexMarkedBoundaryEndpoint n y) := by
      intro hy
      exact hendpoint (vertex_adj_fixed_ghost_mem_markedEndpointLayer
        n radius hradius x y hxy hy.1 hy.2)
    simp [isingBoundaryClamp, hnot]


theorem faceMarkedEndpointClamped_weightedLaplacian_eq_sampled
    (n radius : Nat) (hradius : 2 <= radius)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hendpoint : Not (faceMarkedEndpointLayer n radius (some c))) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c) =
      isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceSampledImaginaryTarget n embedding Phi) (some c) := by
  have hsampled : faceSampledImaginaryTarget n embedding Phi =
      isingFiniteGhostExtension 0 (fun d => (Phi (embedding d)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold faceGhostConductance faceMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some, isingFiniteGhostLaplacian_some]
  have hcvalue : isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
      (fun d => (Phi (embedding d)).im) c = (Phi (embedding c)).im := by
    simp [isingBoundaryClamp, faceMarkedBoundaryEndpoint, hc]
  have hlap := isingFiniteGraphLaplacian_eq_of_eq_on_neighbors
    (fkIsingSquareFullFaceGraph n)
    (isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
      (fun d => (Phi (embedding d)).im))
    (fun d => (Phi (embedding d)).im) c hcvalue
  rw [hlap]
  · rw [hcvalue]
  · intro d hcd
    have hnot : Not (faceMarkedBoundaryEndpoint n d) := by
      intro hd
      exact hendpoint (face_adj_fixed_ghost_mem_markedEndpointLayer
        n radius hradius c d hcd hd.1 hd.2)
    simp [isingBoundaryClamp, hnot]


theorem vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (hrange : forall x,
      0 <= (Phi (embedding x)).im /\ (Phi (embedding x)).im <= 1)
    (x : FKIsingSquareFullVertexNode n) :
    |isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x)| <=
        4 + 3 * isingFermionicGhostCoefficient := by
  let f := isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
    (fun y => (Phi (embedding y)).im)
  have hfrange : forall y, 0 <= f y /\ f y <= 1 := by
    intro y
    by_cases hy : vertexMarkedBoundaryEndpoint n y
    · simp [f, isingBoundaryClamp, hy]
    · simpa [f, isingBoundaryClamp, hy] using hrange y
  have hgraph : |isingFiniteGraphLaplacian
      (fkIsingSquareFullVertexGraph n) f x| <= 4 :=
    isingFiniteGraphLaplacian_abs_le_four_of_unitRange
      (fkIsingSquareFullVertexGraph n) f x
      (fullVertex_neighbor_card_le_four n x) hfrange
  have hjump : |1 - f x| <= 1 := by
    rw [abs_le]
    constructor <;> linarith [(hfrange x).1, (hfrange x).2]
  have hrate0 : 0 <= isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x :=
    isingFermionicGhostRate_nonneg _ x
  have hrate := vertexGhostRate_le_threeCoefficient n x
  unfold vertexGhostConductance vertexMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some]
  change |isingFiniteGraphLaplacian
      (fkIsingSquareFullVertexGraph n) f x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - f x)| <= _
  calc
    |_ + _| <= |isingFiniteGraphLaplacian
        (fkIsingSquareFullVertexGraph n) f x| +
      |isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - f x)| :=
          abs_add_le _ _
    _ <= 4 + (3 * isingFermionicGhostCoefficient) * 1 := by
      rw [abs_mul, abs_of_nonneg hrate0]
      exact add_le_add hgraph
        (mul_le_mul hrate hjump (abs_nonneg _)
          (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
    _ = _ := by ring


theorem faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (hrange : forall c,
      0 <= (Phi (embedding c)).im /\ (Phi (embedding c)).im <= 1)
    (c : FKIsingSquareFullFaceNode n) :
    |isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c)| <=
        4 + 3 * isingFermionicGhostCoefficient := by
  let f := isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
    (fun d => (Phi (embedding d)).im)
  have hfrange : forall d, 0 <= f d /\ f d <= 1 := by
    intro d
    by_cases hd : faceMarkedBoundaryEndpoint n d
    · simp [f, isingBoundaryClamp, hd]
    · simpa [f, isingBoundaryClamp, hd] using hrange d
  have hgraph : |isingFiniteGraphLaplacian
      (fkIsingSquareFullFaceGraph n) f c| <= 4 :=
    isingFiniteGraphLaplacian_abs_le_four_of_unitRange
      (fkIsingSquareFullFaceGraph n) f c
      (fullFace_neighbor_card_le_four n c) hfrange
  have hjump : |0 - f c| <= 1 := by
    rw [abs_le]
    constructor <;> linarith [(hfrange c).1, (hfrange c).2]
  have hrate0 : 0 <= isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n) c :=
    isingFermionicGhostRate_nonneg _ c
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n) c <=
        3 * isingFermionicGhostCoefficient := by
    have h := faceGhostRate_le_coefficient n c
    nlinarith [isingFermionicGhostCoefficient_pos.le]
  unfold faceGhostConductance faceMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some]
  change |isingFiniteGraphLaplacian
      (fkIsingSquareFullFaceGraph n) f c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - f c)| <= _
  calc
    |_ + _| <= |isingFiniteGraphLaplacian
        (fkIsingSquareFullFaceGraph n) f c| +
      |isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - f c)| :=
          abs_add_le _ _
    _ <= 4 + (3 * isingFermionicGhostCoefficient) * 1 := by
      rw [abs_mul, abs_of_nonneg hrate0]
      exact add_le_add hgraph
        (mul_le_mul hrate hjump (abs_nonneg _)
          (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
    _ = _ := by ring


theorem vertexMarkedEndpointClamped_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (traceBound bulkResidual layerResidual endpointResidual : Real)
    (htraceBound : 0 <= traceBound)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (htrace : forall x, fkIsingSquareFullVertexFixedBoundary n x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) ->
        |0 - (Phi (embedding x)).im| <= traceBound)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
        (some x)| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
        (some x)| <= layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
        (some x)| <= endpointResidual) :
    forall z, |vertexDirichlet n hn z -
        vertexMarkedEndpointClampedSampledTarget n embedding Phi z| <=
      traceBound + bulkResidual * vertexExplicitPoissonBarrier n z +
        layerResidual * vertexGhostLayerBarrier n z +
        endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  intro z
  have h := vertexDirichlet_target_error_le_endpointLocalized
    n hn radius (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual hbulkResidual
    hlayerResidual hendpointResidual hbulk hlayer hendpoint z
  have hb := vertexMarkedEndpointClamped_boundaryConsistencyError_le
    n hn embedding Phi traceBound htraceBound htrace
  linarith


theorem faceMarkedEndpointClamped_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (traceBound bulkResidual layerResidual endpointResidual : Real)
    (htraceBound : 0 <= traceBound)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (htrace : forall c, fkIsingSquareFullFaceFixedBoundary n c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) ->
        |1 - (Phi (embedding c)).im| <= traceBound)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi)
        (some c)| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi)
        (some c)| <= layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi)
        (some c)| <= endpointResidual) :
    forall z, |faceDirichlet n hn z -
        faceMarkedEndpointClampedSampledTarget n embedding Phi z| <=
      traceBound + bulkResidual * faceExplicitPoissonBarrier n z +
        layerResidual * faceGhostLayerBarrier n z +
        endpointResidual * faceMarkedEndpointBarrier n radius z := by
  intro z
  have h := faceDirichlet_target_error_le_endpointLocalized
    n hn radius (faceMarkedEndpointClampedSampledTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual hbulkResidual
    hlayerResidual hendpointResidual hbulk hlayer hendpoint z
  have hb := faceMarkedEndpointClamped_boundaryConsistencyError_le
    n hn embedding Phi traceBound htraceBound htrace
  linarith


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
