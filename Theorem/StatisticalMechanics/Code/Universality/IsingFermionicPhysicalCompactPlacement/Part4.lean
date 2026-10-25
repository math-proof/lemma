/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalStripMapTraceRangeData.vertexRange
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k)) :
    0 ≤ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im ∧
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im ≤ 1 := by
  exact H.range (Or.inl ⟨k, x, rfl⟩)

theorem PhysicalStripMapTraceRangeData.faceRange
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k)) :
    0 ≤ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im ∧
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im ≤ 1 := by
  exact H.range (Or.inr ⟨k, c, rfl⟩)

theorem PhysicalStripMapTraceRangeData.vertexFixed
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hx : fkIsingSquareFullVertexFixedBoundary (N k) x) :
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0 :=
  H.lowerTrace (Or.inl ⟨k, x, hx, rfl⟩)

theorem PhysicalStripMapTraceRangeData.faceFixed
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hc : fkIsingSquareFullFaceFixedBoundary (N k) c) :
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1 :=
  H.upperTrace (Or.inl ⟨k, c, hc, rfl⟩)

theorem PhysicalStripMapTraceRangeData.vertexFree
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) :
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1 :=
  H.upperTrace (Or.inr ⟨k, x, hfixed, hghost, rfl⟩)

theorem PhysicalStripMapTraceRangeData.faceFree
    {N : Nat -> Nat} {Phi : Complex -> Complex} {mesh : Nat -> Real}
    (H : PhysicalStripMapTraceRangeData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) :
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0 :=
  H.lowerTrace (Or.inr ⟨k, c, hfixed, hghost, rfl⟩)


theorem PhysicalEndpointLocalizedRobinInputs.ofSegmentLayerAndStripMap
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointSegmentFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (Hstrip : PhysicalStripMapTraceRangeData N Phi mesh)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => 4 * Hlayer.constant * mesh k) (fun _ => 4) := by
  apply PhysicalEndpointLocalizedRobinInputs.ofLocalizedSegmentFourthOrderAndRange
    (fun k => 4 * Hlayer.constant * mesh k) Hfourth hmesh_nonneg
  · intro k
    exact mul_nonneg (mul_nonneg (by norm_num) Hlayer.constant.2)
      (hmesh_nonneg k)
  · exact Hstrip.vertexFixed
  · exact Hstrip.faceFixed
  · exact Hstrip.vertexFree
  · exact Hstrip.faceFree
  · exact Hlayer.vertexLaplacian hmesh_nonneg
  · exact Hlayer.faceLaplacian hmesh_nonneg
  · exact Hstrip.vertexRange
  · exact Hstrip.faceRange
  · exact hscaledFourth_tendsto
  · simpa using tendsto_const_nhds.mul hmesh_tendsto
  · exact hmesh_tendsto


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
