/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part3


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexMarkedEndpointBarrier_nonneg (n radius : Nat) :
    forall z, 0 <= vertexMarkedEndpointBarrier n radius z :=
  isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)

theorem faceMarkedEndpointBarrier_nonneg (n radius : Nat) :
    forall z, 0 <= faceMarkedEndpointBarrier n radius z :=
  isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)

theorem vertexMarkedEndpointBarrier_laplacian_nonpos
    (n radius : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexMarkedEndpointBarrier n radius) z <= 0 := by
  unfold vertexMarkedEndpointBarrier
  by_cases hze : vertexMarkedEndpointLayer n radius z
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
      (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) z hz hze]
    norm_num
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
      (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) z hz hze]

theorem faceMarkedEndpointBarrier_laplacian_nonpos
    (n radius : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceMarkedEndpointBarrier n radius) z <= 0 := by
  unfold faceMarkedEndpointBarrier
  by_cases hze : faceMarkedEndpointLayer n radius z
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
      (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) z hz hze]
    norm_num
  · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
      (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) z hz hze]

theorem vertexMarkedEndpointBarrier_laplacian_le_neg_one
    (n radius : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z))
    (hze : vertexMarkedEndpointLayer n radius z) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexMarkedEndpointBarrier n radius) z <= -1 := by
  unfold vertexMarkedEndpointBarrier
  rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) z hz hze]

theorem faceMarkedEndpointBarrier_laplacian_le_neg_one
    (n radius : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z))
    (hze : faceMarkedEndpointLayer n radius z) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceMarkedEndpointBarrier n radius) z <= -1 := by
  unfold faceMarkedEndpointBarrier
  rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) z hz hze]


theorem vertexDirichlet_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= endpointResidual) :
    forall z, |vertexDirichlet n hn z - target z| <=
      vertexBoundaryConsistencyError n hn target +
        bulkResidual * vertexExplicitPoissonBarrier n z +
        layerResidual * vertexGhostLayerBarrier n z +
        endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  apply isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostLayer n)
    (vertexMarkedEndpointLayer n radius)
    (vertexDirichlet n hn) target
    (vertexExplicitPoissonBarrier n) (vertexGhostLayerBarrier n)
    (vertexMarkedEndpointBarrier n radius)
    (vertexBoundaryConsistencyError n hn target)
    bulkResidual layerResidual endpointResidual
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
    (vertexDirichlet_harmonicOn n hn)
  · intro z hz
    rw [vertexDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target z hz
  · exact hbulkResidual
  · exact hlayerResidual
  · exact hendpointResidual
  · exact vertexExplicitPoissonBarrier_nonneg n
  · exact vertexGhostLayerBarrier_nonneg n
  · exact vertexMarkedEndpointBarrier_nonneg n radius
  · exact vertexExplicitPoissonBarrier_laplacian n hn
  · exact vertexGhostLayerBarrier_laplacian_nonpos n
  · exact vertexGhostLayerBarrier_laplacian_le_neg_one n
  · exact vertexMarkedEndpointBarrier_laplacian_nonpos n radius
  · exact vertexMarkedEndpointBarrier_laplacian_le_neg_one n radius
  · intro z hz hnotLayer hnotEndpoint
    cases z with
    | none => exact False.elim (hz trivial)
    | some x =>
        apply hbulk x hz
        · exact Nat.eq_zero_of_not_pos hnotLayer
        · exact hnotEndpoint
  · intro z hz hLayer hnotEndpoint
    cases z with
    | none => exact False.elim hLayer
    | some x => exact hlayer x hz hLayer hnotEndpoint
  · intro z hz hEndpoint
    cases z with
    | none => exact False.elim hEndpoint
    | some x => exact hendpoint x hz hEndpoint


theorem faceDirichlet_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= endpointResidual) :
    forall z, |faceDirichlet n hn z - target z| <=
      faceBoundaryConsistencyError n hn target +
        bulkResidual * faceExplicitPoissonBarrier n z +
        layerResidual * faceGhostLayerBarrier n z +
        endpointResidual * faceMarkedEndpointBarrier n radius z := by
  apply isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostLayer n)
    (faceMarkedEndpointLayer n radius)
    (faceDirichlet n hn) target
    (faceExplicitPoissonBarrier n) (faceGhostLayerBarrier n)
    (faceMarkedEndpointBarrier n radius)
    (faceBoundaryConsistencyError n hn target)
    bulkResidual layerResidual endpointResidual
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
    (faceDirichlet_harmonicOn n hn)
  · intro z hz
    rw [faceDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) target z hz
  · exact hbulkResidual
  · exact hlayerResidual
  · exact hendpointResidual
  · exact faceExplicitPoissonBarrier_nonneg n
  · exact faceGhostLayerBarrier_nonneg n
  · exact faceMarkedEndpointBarrier_nonneg n radius
  · exact faceExplicitPoissonBarrier_laplacian n
  · exact faceGhostLayerBarrier_laplacian_nonpos n
  · exact faceGhostLayerBarrier_laplacian_le_neg_one n
  · exact faceMarkedEndpointBarrier_laplacian_nonpos n radius
  · exact faceMarkedEndpointBarrier_laplacian_le_neg_one n radius
  · intro z hz hnotLayer hnotEndpoint
    cases z with
    | none => exact False.elim (hz trivial)
    | some c =>
        apply hbulk c hz
        · exact Nat.eq_zero_of_not_pos hnotLayer
        · exact hnotEndpoint
  · intro z hz hLayer hnotEndpoint
    cases z with
    | none => exact False.elim hLayer
    | some c => exact hlayer c hz hLayer hnotEndpoint
  · intro z hz hEndpoint
    cases z with
    | none => exact False.elim hEndpoint
    | some c => exact hendpoint c hz hEndpoint


theorem vertexSampled_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= endpointResidual)
    (hfreeTrace : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      (Phi (embedding x)).im = 1) :
    forall z, |vertexDirichlet n hn z -
        vertexSampledImaginaryTarget n embedding Phi z| <=
      vertexBoundaryConsistencyError n hn
          (vertexSampledImaginaryTarget n embedding Phi) +
        bulkResidual * vertexExplicitPoissonBarrier n z +
        layerResidual * vertexGhostLayerBarrier n z +
        endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  apply vertexDirichlet_target_error_le_endpointLocalized n hn radius
    (vertexSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual
    hbulkResidual hlayerResidual hendpointResidual
  · intro x hx hzero hnotEndpoint
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using
      hbulk x hx hzero hnotEndpoint
  · intro x hx hpos hnotEndpoint
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace x hx hpos]
    simpa using hlayer x hx hpos hnotEndpoint
  · intro x hx hEndpoint
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    by_cases hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x
    · rw [hfreeTrace x hx hpos]
      simpa using hendpoint x hx hEndpoint
    · have hzero : fkIsingSquareFullVertexGhostMultiplicity n x = 0 :=
        Nat.eq_zero_of_not_pos hpos
      simpa [isingFermionicGhostRate, hzero] using
        hendpoint x hx hEndpoint


theorem faceSampled_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= endpointResidual)
    (hfreeTrace : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      (Phi (embedding c)).im = 0) :
    forall z, |faceDirichlet n hn z -
        faceSampledImaginaryTarget n embedding Phi z| <=
      faceBoundaryConsistencyError n hn
          (faceSampledImaginaryTarget n embedding Phi) +
        bulkResidual * faceExplicitPoissonBarrier n z +
        layerResidual * faceGhostLayerBarrier n z +
        endpointResidual * faceMarkedEndpointBarrier n radius z := by
  apply faceDirichlet_target_error_le_endpointLocalized n hn radius
    (faceSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual
    hbulkResidual hlayerResidual hendpointResidual
  · intro c hc hzero hnotEndpoint
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using
      hbulk c hc hzero hnotEndpoint
  · intro c hc hpos hnotEndpoint
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace c hc hpos]
    simpa using hlayer c hc hpos hnotEndpoint
  · intro c hc hEndpoint
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    by_cases hpos : 0 < fkIsingSquareFullFaceGhostMultiplicity n c
    · rw [hfreeTrace c hc hpos]
      simpa using hendpoint c hc hEndpoint
    · have hzero : fkIsingSquareFullFaceGhostMultiplicity n c = 0 :=
        Nat.eq_zero_of_not_pos hpos
      simpa [isingFermionicGhostRate, hzero] using
        hendpoint c hc hEndpoint


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
