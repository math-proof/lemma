/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2


namespace StatMech.Universality

open Filter

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointVariableLayerIncrementData.vertexLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
    (hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x)
    (hendpoint : Not (vertexMarkedEndpointLayer
      (N k) (radius k) (some x))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y => (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| <= 4 * H.constant k * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullVertexGraph (N k))
    (fun y => (Phi (fullSquareScaledVertexEmbedding
      (N k) (mesh k) y)).im) x (H.constant k * mesh k)
    (mul_nonneg (H.constant k).2 (hmesh k))
    (fullVertex_neighbor_card_le_four (N k) x)
    (H.vertex k x hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound

theorem PhysicalEndpointVariableLayerIncrementData.faceLaplacian
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (H : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius)
    (hmesh : forall k, 0 <= mesh k) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
    (hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c)
    (hendpoint : Not (faceMarkedEndpointLayer
      (N k) (radius k) (some c))) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d => (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| <= 4 * H.constant k * mesh k := by
  have hbound := isingFiniteGraphLaplacian_abs_le_four_mul
    (fkIsingSquareFullFaceGraph (N k))
    (fun d => (Phi (fullSquareScaledFaceEmbedding
      (N k) (mesh k) d)).im) c (H.constant k * mesh k)
    (mul_nonneg (H.constant k).2 (hmesh k))
    (fullFace_neighbor_card_le_four (N k) c)
    (H.face k c hfixed hghost hendpoint)
  simpa [mul_assoc] using hbound


theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofVariableFourthOrderLayerTraceAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {traceRate : Nat -> Real}
    (Hfourth : PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointVariableLayerIncrementData N Phi mesh radius)
    (Htrace : PhysicalEndpointOrdinaryTraceData N Phi mesh radius traceRate)
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto (fun k =>
      ((Hfourth.boundOne k + Hfourth.boundTwo k) * |mesh k| ^ 4 / 12) *
        (N k : Real) ^ 2) atTop (nhds 0))
    (hlayer_tendsto : Tendsto (fun k =>
      (Hlayer.constant k : Real) * mesh k) atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      traceRate
      (fun k =>
        (Hfourth.boundOne k + Hfourth.boundTwo k) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant k) * mesh k +
        (3 * isingFermionicGhostCoefficient) * traceRate k)
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  apply PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals
    hvertexRadius hfaceRadius
  · exact Htrace.trace_nonneg
  · intro k
    exact div_nonneg
      (mul_nonneg (Hfourth.boundSum_nonneg k)
        (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · intro k
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Hlayer.constant k).2)
        (hmesh_nonneg k))
      (mul_nonneg
        (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        (Htrace.trace_nonneg k))
  · intro _
    nlinarith [isingFermionicGhostCoefficient_pos.le]
  · exact Htrace.vertexFixed
  · exact Htrace.faceFixed
  · intro k x hfixed hghost hendpoint
    have htarget : vertexSampledImaginaryTarget (N k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 1
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, vertexGhostConductance, isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hghost] using
      Hfourth.vertexLaplacian k x hfixed hghost hendpoint
  · intro k c hfixed hghost hendpoint
    have htarget : faceSampledImaginaryTarget (N k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 0
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, faceGhostConductance, isingFiniteGhostLaplacian_some]
    simpa [isingFermionicGhostRate, hghost] using
      Hfourth.faceLaplacian k c hfixed hghost hendpoint
  · intro k x hfixed hghost hendpoint
    have htarget : vertexSampledImaginaryTarget (N k)
        (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 1
        (fun y => (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, vertexGhostConductance, isingFiniteGhostLaplacian_some]
    have hgraph := Hlayer.vertexLaplacian hmesh_nonneg
      k x hfixed hghost hendpoint
    have hrate0 := isingFermionicGhostRate_nonneg
      (fkIsingSquareFullVertexGhostMultiplicity (N k)) x
    have hrate := vertexGhostRate_le_threeCoefficient (N k) x
    calc
      |_ + _| <= |isingFiniteGraphLaplacian
          (fkIsingSquareFullVertexGraph (N k))
          (fun y => (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| +
        |isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (fullSquareScaledVertexEmbedding
              (N k) (mesh k) x)).im)| := abs_add_le _ _
      _ <= 4 * Hlayer.constant k * mesh k +
          (3 * isingFermionicGhostCoefficient) * traceRate k := by
        rw [abs_mul, abs_of_nonneg hrate0]
        exact add_le_add hgraph
          (mul_le_mul hrate (Htrace.vertexFree k x hfixed hghost hendpoint)
            (abs_nonneg _)
            (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
  · intro k c hfixed hghost hendpoint
    have htarget : faceSampledImaginaryTarget (N k)
        (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi =
      isingFiniteGhostExtension 0
        (fun d => (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) := by
      funext z
      cases z <;> rfl
    rw [htarget, faceGhostConductance, isingFiniteGhostLaplacian_some]
    have hgraph := Hlayer.faceLaplacian hmesh_nonneg
      k c hfixed hghost hendpoint
    have hrate0 := isingFermionicGhostRate_nonneg
      (fkIsingSquareFullFaceGhostMultiplicity (N k)) c
    have hrate : isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity (N k)) c <=
          3 * isingFermionicGhostCoefficient := by
      have h := faceGhostRate_le_coefficient (N k) c
      nlinarith [isingFermionicGhostCoefficient_pos.le]
    calc
      |_ + _| <= |isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph (N k))
          (fun d => (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| +
        |isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (fullSquareScaledFaceEmbedding
              (N k) (mesh k) c)).im)| := abs_add_le _ _
      _ <= 4 * Hlayer.constant k * mesh k +
          (3 * isingFermionicGhostCoefficient) * traceRate k := by
        rw [abs_mul, abs_of_nonneg hrate0]
        exact add_le_add hgraph
          (mul_le_mul hrate (Htrace.faceFree k c hfixed hghost hendpoint)
            (abs_nonneg _)
            (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
  · intro k x _hfixed _hendpoint
    exact vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
      (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
      (hvertexRange k) x
  · intro k c _hfixed _hendpoint
    exact faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
      (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
      (hfaceRange k) c
  · exact Htrace.trace_tendsto
  · exact hscaledFourth_tendsto
  · have hmeshPart : Tendsto
        (fun k => (4 * (Hlayer.constant k : Real)) * mesh k)
        atTop (nhds 0) := by
      simpa [mul_assoc] using tendsto_const_nhds.mul hlayer_tendsto
    have htracePart : Tendsto
        (fun k => (3 * isingFermionicGhostCoefficient) * traceRate k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul Htrace.trace_tendsto
    simpa using hmeshPart.add htracePart

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
