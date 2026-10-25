/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk


namespace StatMech.Universality

open Filter

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointVariableFourthOrderBulkData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <=
        (H.boundOne k + H.boundTwo k) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    (N k) (mesh k) (fun z => (Phi z).im) x
      heast hnorth hwest hsouth]
  exact (H.vertex k x hfixed hghost hendpoint).stencil

theorem PhysicalEndpointVariableFourthOrderBulkData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <=
        (H.boundOne k + H.boundTwo k) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    (N k) (mesh k) (fun z => (Phi z).im) c
      heast hnorth hwest hsouth]
  exact (H.face k c hfixed hghost hendpoint).stencil


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
