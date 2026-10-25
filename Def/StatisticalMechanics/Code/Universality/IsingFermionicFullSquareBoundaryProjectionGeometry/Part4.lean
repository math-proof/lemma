/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part3


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierTraces
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (N k) (mesh k) (radius k)))
    (hvertexFixedTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        (Phi (fullSquareVertexBoundaryProjection
          (N k) (mesh k) x)).im = 0)
    (hfaceFixedTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c)).im = 1)
    (hvertexFreeTrace : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        (Phi (fullSquareVertexFreeBoundaryProjection
          (N k) (mesh k) x)).im = 1)
    (hfaceFreeTrace : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        (Phi (fullSquareFaceFreeBoundaryProjection
          (N k) (mesh k) c)).im = 0) :
    FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius where
  lipschitzConstant := L
  region k := fullSquareOrdinaryBoundaryProjectionCarrier
    (N k) (mesh k) (radius k)
  imPhi_lipschitz := hPhi
  vertexFixed k x hfixed hghost :=
    ⟨Or.inl ⟨x, hfixed, hghost, Or.inl rfl⟩,
      hvertexFixedTrace k x hfixed hghost⟩
  faceFixed k c hfixed hghost :=
    ⟨Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inl rfl⟩),
      Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inr rfl⟩),
      hfaceFixedTrace k c hfixed hghost⟩
  vertexFree k x hfixed hghost hendpoint :=
    ⟨Or.inr (Or.inr (Or.inl
      ⟨x, hfixed, hghost, hendpoint, Or.inl rfl⟩)),
      hvertexFreeTrace k x hfixed hghost hendpoint⟩
  faceFree k c hfixed hghost hendpoint :=
    ⟨Or.inr (Or.inr (Or.inr
        ⟨c, hfixed, hghost, hendpoint, Or.inl rfl⟩)),
      Or.inr (Or.inr (Or.inr
        ⟨c, hfixed, hghost, hendpoint, Or.inr rfl⟩)),
      hfaceFreeTrace k c hfixed hghost hendpoint⟩


noncomputable def
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierSideTraces
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (N k) (mesh k) (radius k)))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide (N k) (mesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides (N k) (mesh k))) :
    FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius :=
  FullSquareOrdinaryBoundaryProjectionTraceData.ofSideTraces
    L (fun k => fullSquareOrdinaryBoundaryProjectionCarrier
      (N k) (mesh k) (radius k))
    hPhi hleftTrace hfreeTrace
    (fun _k x hfixed hghost =>
      Or.inl ⟨x, hfixed, hghost, Or.inl rfl⟩)
    (fun _k c hfixed hghost =>
      ⟨Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inl rfl⟩),
        Or.inr (Or.inl ⟨c, hfixed, hghost, Or.inr rfl⟩)⟩)
    (fun _k x hfixed hghost hendpoint =>
      Or.inr (Or.inr (Or.inl
        ⟨x, hfixed, hghost, hendpoint, Or.inl rfl⟩)))
    (fun _k c hfixed hghost hendpoint =>
      ⟨Or.inr (Or.inr (Or.inr
          ⟨c, hfixed, hghost, hendpoint, Or.inl rfl⟩)),
        Or.inr (Or.inr (Or.inr
          ⟨c, hfixed, hghost, hendpoint, Or.inr rfl⟩))⟩)


noncomputable def
    FullSquareOrdinaryBoundaryProjectionTraceData.toProjectionData
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) :
    PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius where
  lipschitzConstant := H.lipschitzConstant
  region := H.region
  imPhi_lipschitz := H.imPhi_lipschitz
  vertexFixed k x hfixed hghost := by
    obtain ⟨hsample, htrace⟩ := H.vertexFixed k x hfixed hghost
    exact
      { boundaryPoint := fullSquareVertexBoundaryProjection
          (N k) (mesh k) x
        sample_mem := hsample
        boundary_mem := by
          simpa [fullSquareVertexBoundaryProjection] using hsample
        trace := htrace
        dist_le_mesh := by
          rw [fullSquareVertexBoundaryProjection_dist]
          exact hmesh k }
  faceFixed k c hfixed hghost := by
    obtain ⟨hsample, hboundary, htrace⟩ := H.faceFixed k c hfixed hghost
    exact
      { boundaryPoint := fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c
        sample_mem := hsample
        boundary_mem := hboundary
        trace := htrace
        dist_le_mesh := fullSquareFaceFixedBoundaryProjection_dist_le
          (N k) (mesh k) (hmesh k) c }
  vertexFree k x hfixed hghost hendpoint := by
    obtain ⟨hsample, htrace⟩ :=
      H.vertexFree k x hfixed hghost hendpoint
    exact
      { boundaryPoint := fullSquareVertexFreeBoundaryProjection
          (N k) (mesh k) x
        sample_mem := hsample
        boundary_mem := by
          simpa [fullSquareVertexFreeBoundaryProjection] using hsample
        trace := htrace
        dist_le_mesh := by
          rw [fullSquareVertexFreeBoundaryProjection_dist]
          exact hmesh k }
  faceFree k c hfixed hghost hendpoint := by
    obtain ⟨hsample, hboundary, htrace⟩ :=
      H.faceFree k c hfixed hghost hendpoint
    exact
      { boundaryPoint := fullSquareFaceFreeBoundaryProjection
          (N k) (mesh k) c
        sample_mem := hsample
        boundary_mem := hboundary
        trace := htrace
        dist_le_mesh := fullSquareFaceFreeBoundaryProjection_dist_le
          (N k) (mesh k) (hmesh k) c }


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
