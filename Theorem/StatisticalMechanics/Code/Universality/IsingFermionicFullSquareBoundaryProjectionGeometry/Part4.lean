/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part4


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierTracesAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
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
          (N k) (mesh k) c)).im = 0)
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (htrace_tendsto : Tendsto
      (fun k => (L k : Real) * mesh k) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      (fun k => (L k : Real) * mesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) * ((L k : Real) * mesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  let Htrace : FullSquareOrdinaryBoundaryProjectionTraceData
      N Phi mesh radius :=
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierTraces
      L hPhi hvertexFixedTrace hfaceFixedTrace hvertexFreeTrace hfaceFreeTrace
  let P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius :=
    Htrace.toProjectionData hmesh_nonneg
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange
      Hfourth Hlayer P hvertexRadius hfaceRadius hmesh_nonneg
      hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto
      hmesh_tendsto


theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
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
        (fullSquareScaledFreeSides (N k) (mesh k)))
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (htrace_tendsto : Tendsto
      (fun k => (L k : Real) * mesh k) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      (fun k => (L k : Real) * mesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) * ((L k : Real) * mesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  let Htrace : FullSquareOrdinaryBoundaryProjectionTraceData
      N Phi mesh radius :=
    FullSquareOrdinaryBoundaryProjectionTraceData.ofCarrierSideTraces
      L hPhi hleftTrace hfreeTrace
  let P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius :=
    Htrace.toProjectionData hmesh_nonneg
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange
      Hfourth Hlayer P hvertexRadius hfaceRadius hmesh_nonneg
      hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto
      hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
