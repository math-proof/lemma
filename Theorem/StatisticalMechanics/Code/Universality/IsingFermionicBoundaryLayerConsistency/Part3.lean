/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexGhostLayerBarrier_laplacian_nonpos
    (n : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexGhostLayerBarrier n) z <= 0 := by
  cases z with
  | none => exact False.elim (hz trivial)
  | some x =>
      rw [vertexGhostLayerBarrier_laplacian]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem faceGhostLayerBarrier_laplacian_nonpos
    (n : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z)) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceGhostLayerBarrier n) z <= 0 := by
  cases z with
  | none => exact False.elim (hz trivial)
  | some c =>
      rw [faceGhostLayerBarrier_laplacian]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem vertexGhostLayerBarrier_laplacian_le_neg_one
    (n : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : Not (vertexDirichletBoundary n z))
    (hlayer : vertexGhostLayer n z) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexGhostLayerBarrier n) z <= -1 := by
  cases z with
  | none => exact False.elim hlayer
  | some x =>
      rw [vertexGhostLayerBarrier_laplacian]
      have hm : (1 : Real) <=
          (fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlayer))
      linarith

theorem faceGhostLayerBarrier_laplacian_le_neg_one
    (n : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : Not (faceDirichletBoundary n z))
    (hlayer : faceGhostLayer n z) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceGhostLayerBarrier n) z <= -1 := by
  cases z with
  | none => exact False.elim hlayer
  | some c =>
      rw [faceGhostLayerBarrier_laplacian]
      have hm : (1 : Real) <=
          (fkIsingSquareFullFaceGhostMultiplicity n c : Real) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlayer))
      linarith


theorem vertexDirichlet_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        target (some x)| <= layerResidual) :
    forall z, |vertexDirichlet n hn z - target z| <=
      vertexBoundaryConsistencyError n hn target +
        bulkResidual * vertexExplicitPoissonBarrierBound n +
        layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply isingFiniteWeighted_harmonic_approximation_of_layer_barriers
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostLayer n)
    (vertexDirichlet n hn) target
    (vertexExplicitPoissonBarrier n) (vertexGhostLayerBarrier n)
    (vertexBoundaryConsistencyError n hn target)
    bulkResidual layerResidual
    (vertexExplicitPoissonBarrierBound n)
    (1 / isingFermionicGhostCoefficient)
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
  · exact vertexExplicitPoissonBarrier_nonneg n
  · exact vertexGhostLayerBarrier_nonneg n
  · exact vertexExplicitPoissonBarrier_le_bound n
  · exact vertexGhostLayerBarrier_le n
  · exact vertexExplicitPoissonBarrier_laplacian n hn
  · exact vertexGhostLayerBarrier_laplacian_nonpos n
  · exact vertexGhostLayerBarrier_laplacian_le_neg_one n
  · intro z hz hnotLayer
    cases z with
    | none => exact False.elim (hz trivial)
    | some x =>
        apply hbulk x hz
        exact Nat.eq_zero_of_not_pos hnotLayer
  · intro z hz hLayer
    cases z with
    | none => exact False.elim hLayer
    | some x => exact hlayer x hz hLayer


theorem faceDirichlet_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        target (some c)| <= layerResidual) :
    forall z, |faceDirichlet n hn z - target z| <=
      faceBoundaryConsistencyError n hn target +
        bulkResidual * faceExplicitPoissonBarrierBound n +
        layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply isingFiniteWeighted_harmonic_approximation_of_layer_barriers
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostLayer n)
    (faceDirichlet n hn) target
    (faceExplicitPoissonBarrier n) (faceGhostLayerBarrier n)
    (faceBoundaryConsistencyError n hn target)
    bulkResidual layerResidual
    (faceExplicitPoissonBarrierBound n)
    (1 / isingFermionicGhostCoefficient)
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
  · exact faceExplicitPoissonBarrier_nonneg n
  · exact faceGhostLayerBarrier_nonneg n
  · exact faceExplicitPoissonBarrier_le_bound n
  · exact faceGhostLayerBarrier_le n
  · exact faceExplicitPoissonBarrier_laplacian n
  · exact faceGhostLayerBarrier_laplacian_nonpos n
  · exact faceGhostLayerBarrier_laplacian_le_neg_one n
  · intro z hz hnotLayer
    cases z with
    | none => exact False.elim (hz trivial)
    | some c =>
        apply hbulk c hz
        exact Nat.eq_zero_of_not_pos hnotLayer
  · intro z hz hLayer
    cases z with
    | none => exact False.elim hLayer
    | some c => exact hlayer c hz hLayer


theorem vertexSampled_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= layerResidual)
    (hfreeTrace : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      (Phi (embedding x)).im = 1) :
    forall z,
      |vertexDirichlet n hn z -
          vertexSampledImaginaryTarget n embedding Phi z| <=
        vertexBoundaryConsistencyError n hn
            (vertexSampledImaginaryTarget n embedding Phi) +
          bulkResidual * vertexExplicitPoissonBarrierBound n +
          layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply vertexDirichlet_target_error_le_split n hn
    (vertexSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual hbulkResidual hlayerResidual
  · intro x hx hzero
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using hbulk x hx hzero
  · intro x hx hpos
    have htarget : vertexSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 1
          (fun y => (Phi (embedding y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold vertexGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace x hx hpos]
    simpa using hlayer x hx hpos


theorem faceSampled_target_error_le_split
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (bulkResidual layerResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= layerResidual)
    (hfreeTrace : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      (Phi (embedding c)).im = 0) :
    forall z,
      |faceDirichlet n hn z -
          faceSampledImaginaryTarget n embedding Phi z| <=
        faceBoundaryConsistencyError n hn
            (faceSampledImaginaryTarget n embedding Phi) +
          bulkResidual * faceExplicitPoissonBarrierBound n +
          layerResidual * (1 / isingFermionicGhostCoefficient) := by
  apply faceDirichlet_target_error_le_split n hn
    (faceSampledImaginaryTarget n embedding Phi)
    bulkResidual layerResidual hbulkResidual hlayerResidual
  · intro c hc hzero
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hzero] using hbulk c hc hzero
  · intro c hc hpos
    have htarget : faceSampledImaginaryTarget n embedding Phi =
        isingFiniteGhostExtension 0
          (fun d => (Phi (embedding d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget]
    unfold faceGhostConductance
    rw [isingFiniteGhostLaplacian_some, hfreeTrace c hc hpos]
    simpa using hlayer c hc hpos

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
