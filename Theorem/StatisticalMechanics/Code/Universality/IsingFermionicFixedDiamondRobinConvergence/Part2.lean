/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionAnalyticCollar
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialPointGreen
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFixedDiamondRobinConvergence


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fixedDiamond_incidence_im_mismatch_le
    {Phi : Complex -> Complex} (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im)
      isingFermionicFixedClosedDiamond)
    (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicProjectionPolynomialSide_pos k)) :
    |(Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k)
        (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e))).im -
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k)
        (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e))).im| <=
      (L : Real) * isingFermionicFixedDiamondMesh k := by
  let c := fkIsingSquareFullFaceOfRadialIncidence
    (isingFermionicProjectionPolynomialSide k)
    (isingFermionicProjectionPolynomialSide_pos k) e
  let x := fkIsingSquareInteriorRadialEndpoint
    (isingFermionicProjectionPolynomialSide k)
    (isingFermionicProjectionPolynomialSide_pos k) e
  rw [← Real.dist_eq]
  calc
    dist
        (Phi (fullSquareScaledFaceEmbedding
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) c)).im
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) x)).im <=
        L * dist
          (fullSquareScaledFaceEmbedding
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicFixedDiamondMesh k) c)
          (fullSquareScaledVertexEmbedding
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicFixedDiamondMesh k) x) :=
      hPhi.dist_le_mul _
        (fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k c) _
        (fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k x)
    _ <= L * isingFermionicFixedDiamondMesh k := by
      gcongr
      exact fullSquareScaledEmbedding_incidenceDistance
        isingFermionicProjectionPolynomialSide
        isingFermionicProjectionPolynomialSide_pos
        isingFermionicFixedDiamondMesh
        isingFermionicFixedDiamondMesh_nonneg k e


theorem primitive_convergence_away_fixedDiamond_of_analyticCollar_lipschitz
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (L : NNReal)
    (hPhiLip : LipschitzOnWith L (fun z => (Phi z).im)
      isingFermionicFixedClosedDiamond)
    (U : Set Complex)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hrangeU : Set.MapsTo Phi U isingFermionicClosedUnitStrip)
    (hcollar : forall k c,
      c ∈ fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k) ->
        ball c (isingFermionicFixedDiamondEndpointCollar k) ⊆ U)
    (hlowerTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondOrdinaryLowerTraceCarrier)
    (hupperTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondOrdinaryUpperTraceCarrier)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip) :
    forall eta : Real, 0 < eta -> Filter.Eventually (fun k =>
      forall e : FKIsingSquareInteriorRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k),
        PhysicalProjectionPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k)
                (isingFermionicFixedDiamondMesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k)
                (isingFermionicFixedDiamondMesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta)
      atTop := by
  let Hlayer := fixedDiamondLayerIncrementDataOfLipschitz L hPhiLip
  have hcarrierLip : forall k,
      LipschitzOnWith
        (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k)
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)) := by
    intro k
    let K := fullSquareOrdinaryBoundaryProjectionCarrier
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicFixedDiamondMesh k)
      (isingFermionicProjectionPolynomialRadius k)
    have hLip := isingFermionic_unitStrip_lipschitzOn_carrier_of_balls
      Phi K (isingFermionicFixedDiamondEndpointCollar k)
      (isingFermionicFixedDiamondEndpointCollar_pos k)
      (fun c hc => hPhi.differentiableOn.mono (hcollar k c hc))
      (fun c hc z hz => hrangeU (hcollar k c hc hz))
      (fun z hz => hrangeU (hcollar k z hz
        (Metric.mem_ball_self
          (isingFermionicFixedDiamondEndpointCollar_pos k))))
    have hconstant :
        isingFermionicFixedDiamondEndpointLipschitzConstant 8 k =
          (⟨8 / isingFermionicFixedDiamondEndpointCollar k,
            (div_pos (by norm_num)
              (isingFermionicFixedDiamondEndpointCollar_pos k)).le⟩ : NNReal) := by
      ext
      exact isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq k
    rw [hconstant]
    exact hLip
  let H :=
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndRangeWith
      Hfourth Hlayer
      (isingFermionicFixedDiamondEndpointLipschitzConstant 8)
      hcarrierLip
      (fun k x hfixed hghost => hlowerTrace
        (Or.inl ⟨k, x, hfixed, hghost, rfl⟩))
      (fun k c hfixed hghost => hupperTrace
        (Or.inl ⟨k, c, hfixed, hghost, rfl⟩))
      (fun k x hfixed hghost hendpoint => hupperTrace
        (Or.inr ⟨k, x, hfixed, hghost, hendpoint, rfl⟩))
      (fun k c hfixed hghost hendpoint => hlowerTrace
        (Or.inr ⟨k, c, hfixed, hghost, hendpoint, rfl⟩))
      (PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges
        hrange).1
      (PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges
        hrange).2
      (tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh 8)
  apply H.primitive_convergence_away_fixedDiamond
    (fun k => (L : Real) * isingFermionicFixedDiamondMesh k)
  · intro k
    exact mul_nonneg L.2 (isingFermionicFixedDiamondMesh_nonneg k)
  · intro k e _hsafe
    exact fixedDiamond_incidence_im_mismatch_le L hPhiLip k e
  · simpa using
      tendsto_const_nhds.mul tendsto_isingFermionicFixedDiamondMesh

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
