/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def
    PhysicalEndpointLocalizedRobinInputs.ofAnalyticOnCompactCentersAndStripMap
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (epsilon : Real) (hcollar : Metric.cthickening epsilon K ⊆ U)
    (Hstrip : PhysicalStripMapTraceRangeData N Phi mesh)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hmesh_collar : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        let H :=
          PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactCenters
            U K hU hK hPhi epsilon hcollar hmesh_collar
              (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
              (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k =>
        let H :=
          PhysicalEndpointLayerIncrementData.ofAnalyticOnCompactCenters
            U K hU hK hPhi epsilon hcollar hmesh_nonneg hmesh_collar
              (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
              (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
        4 * H.constant * mesh k)
      (fun _ => 4) := by
  let Hfourth : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius :=
    PhysicalEndpointSegmentFourthOrderBulkData.ofAnalyticOnCompactCenters
      U K hU hK hPhi epsilon hcollar hmesh_collar
        (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
        (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
  let Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius :=
    PhysicalEndpointLayerIncrementData.ofAnalyticOnCompactCenters
      U K hU hK hPhi epsilon hcollar hmesh_nonneg hmesh_collar
        (fun k x hfixed _ hendpoint => hvertex k x hfixed hendpoint)
        (fun k c hfixed _ hendpoint => hface k c hfixed hendpoint)
  exact PhysicalEndpointLocalizedRobinInputs.ofSegmentLayerAndStripMap
    Hfourth Hlayer Hstrip hmesh_nonneg hscaledFourth_tendsto hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
