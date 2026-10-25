/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCalibratedRobinConsistency
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility


namespace StatMech.Universality

open Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalFourthOrderBulkData.vertexLaplacian
    {N : Nat → Nat} {Phi : Complex → Complex} {mesh : Nat → Real}
    (H : PhysicalFourthOrderBulkData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : ¬ fkIsingSquareFullVertexFixedBoundary (N k) x)
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| ≤
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.vertex k x hfixed hghost
  exact fullSquareScaledVertex_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z ↦ (Phi z).im) x
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic

theorem PhysicalFourthOrderBulkData.faceLaplacian
    {N : Nat → Nat} {Phi : Complex → Complex} {mesh : Nat → Real}
    (H : PhysicalFourthOrderBulkData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : ¬ fkIsingSquareFullFaceFixedBoundary (N k) c)
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| ≤
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.face k c hfixed hghost
  exact fullSquareScaledFace_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z ↦ (Phi z).im) c
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
