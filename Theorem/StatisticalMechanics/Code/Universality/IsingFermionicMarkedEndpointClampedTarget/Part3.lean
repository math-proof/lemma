/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectedPrimitiveConvergence
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointClampedTarget


namespace StatMech.Universality

open Filter

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hboundary_nonneg : forall k, 0 <= boundaryRate k)
    (hbulk_nonneg : forall k, 0 <= bulkRate k)
    (hlayer_nonneg : forall k, 0 <= layerRate k)
    (hendpoint_nonneg : forall k, 0 <= endpointRate k)
    (hvertexTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        |0 - (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im| <= boundaryRate k)
    (hfaceTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        |1 - (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im| <= boundaryRate k)
    (hvertexBulk : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
          (vertexSampledImaginaryTarget (N k)
            (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
          (some x)| <= bulkRate k)
    (hfaceBulk : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
          (faceSampledImaginaryTarget (N k)
            (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
          (some c)| <= bulkRate k)
    (hvertexLayer : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
          (vertexSampledImaginaryTarget (N k)
            (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
          (some x)| <= layerRate k)
    (hfaceLayer : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
          (faceSampledImaginaryTarget (N k)
            (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
          (some c)| <= layerRate k)
    (hvertexEndpoint : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      vertexMarkedEndpointLayer (N k) (radius k) (some x) ->
        |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
          (vertexMarkedEndpointClampedSampledTarget (N k)
            (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
          (some x)| <= endpointRate k)
    (hfaceEndpoint : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      faceMarkedEndpointLayer (N k) (radius k) (some c) ->
        |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
          (faceMarkedEndpointClampedSampledTarget (N k)
            (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
          (some c)| <= endpointRate k)
    (hboundary_tendsto : Tendsto boundaryRate atTop (nhds 0))
    (hscaledBulk_tendsto : Tendsto
      (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0))
    (hlayer_tendsto : Tendsto layerRate atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      boundaryRate bulkRate layerRate endpointRate := by
  refine
    { boundary_nonneg := hboundary_nonneg
      bulk_nonneg := hbulk_nonneg
      layer_nonneg := hlayer_nonneg
      endpoint_nonneg := hendpoint_nonneg
      vertexTrace := hvertexTrace
      faceTrace := hfaceTrace
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := ?_
      faceLayer := ?_
      vertexEndpoint := hvertexEndpoint
      faceEndpoint := hfaceEndpoint
      boundary_tendsto := hboundary_tendsto
      scaledBulk_tendsto := hscaledBulk_tendsto
      layer_tendsto := hlayer_tendsto }
  · intro k x hx hghost hendpoint
    rw [vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hvertexRadius k)
      (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi x hx hendpoint]
    exact hvertexBulk k x hx hghost hendpoint
  · intro k c hc hghost hendpoint
    rw [faceMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hfaceRadius k)
      (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi c hc hendpoint]
    exact hfaceBulk k c hc hghost hendpoint
  · intro k x hx hghost hendpoint
    rw [vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hvertexRadius k)
      (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi x hx hendpoint]
    exact hvertexLayer k x hx hghost hendpoint
  · intro k c hc hghost hendpoint
    rw [faceMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hfaceRadius k)
      (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi c hc hendpoint]
    exact hfaceLayer k c hc hghost hendpoint

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.vertex_error_le
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh
      radius boundaryRate bulkRate layerRate endpointRate)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x)) :
    |vertexDirichlet (N k) (hN k) (some x) -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
      boundaryRate k + bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) +
        layerRate k * vertexGhostLayerBarrier (N k) (some x) +
        endpointRate k * vertexMarkedEndpointBarrier
          (N k) (radius k) (some x) := by
  have h := vertexMarkedEndpointClamped_target_error_le_endpointLocalized
    (N k) (hN k) (radius k)
    (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
    (boundaryRate k) (bulkRate k) (layerRate k) (endpointRate k)
    (H.boundary_nonneg k) (H.bulk_nonneg k) (H.layer_nonneg k)
    (H.endpoint_nonneg k) (H.vertexTrace k) (H.vertexBulk k)
    (H.vertexLayer k) (H.vertexEndpoint k) (some x)
  simpa [vertexMarkedEndpointClampedSampledTarget_of_not_fixed _ _ _ x hx]
    using h

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.face_error_le
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh
      radius boundaryRate bulkRate layerRate endpointRate)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c)) :
    |faceDirichlet (N k) (hN k) (some c) -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
      boundaryRate k + bulkRate k * faceExplicitPoissonBarrier (N k) (some c) +
        layerRate k * faceGhostLayerBarrier (N k) (some c) +
        endpointRate k * faceMarkedEndpointBarrier
          (N k) (radius k) (some c) := by
  have h := faceMarkedEndpointClamped_target_error_le_endpointLocalized
    (N k) (hN k) (radius k)
    (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
    (boundaryRate k) (bulkRate k) (layerRate k) (endpointRate k)
    (H.boundary_nonneg k) (H.bulk_nonneg k) (H.layer_nonneg k)
    (H.endpoint_nonneg k) (H.faceTrace k) (H.faceBulk k)
    (H.faceLayer k) (H.faceEndpoint k) (some c)
  simpa [faceMarkedEndpointClampedSampledTarget_of_not_fixed _ _ _ c hc]
    using h


theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh
      radius boundaryRate bulkRate layerRate endpointRate)
    (safe : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
    (vertexEndpointWeight faceEndpointWeight mismatchRate : Nat -> Real)
    (hvertexWeight_nonneg : forall k, 0 <= vertexEndpointWeight k)
    (hfaceWeight_nonneg : forall k, 0 <= faceEndpointWeight k)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hsafeVertex : forall k e, safe k e ->
      Not (fkIsingSquareFullVertexFixedBoundary (N k)
        (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)))
    (hsafeFace : forall k e, safe k e ->
      Not (fkIsingSquareFullFaceFixedBoundary (N k)
        (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)))
    (hvertexWeight : forall k e, safe k e ->
      vertexMarkedEndpointBarrier (N k) (radius k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <=
          vertexEndpointWeight k)
    (hfaceWeight : forall k e, safe k e ->
      faceMarkedEndpointBarrier (N k) (radius k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) <=
          faceEndpointWeight k)
    (hmismatch : forall k e, safe k e ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <=
        mismatchRate k)
    (hvertexEndpoint_tendsto : Tendsto
      (fun k => endpointRate k * vertexEndpointWeight k)
      atTop (nhds 0))
    (hfaceEndpoint_tendsto : Tendsto
      (fun k => endpointRate k * faceEndpointWeight k)
      atTop (nhds 0))
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        safe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  let common : Nat -> Real := fun k =>
    boundaryRate k +
      vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
      (1 / isingFermionicGhostCoefficient) * layerRate k
  let upper : Nat -> Real := fun k =>
    common k + endpointRate k * vertexEndpointWeight k +
      endpointRate k * faceEndpointWeight k + mismatchRate k
  have hbulk : Tendsto
      (fun k => vertexBarrierGrowthConstant *
        (bulkRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul H.scaledBulk_tendsto
  have hlayer : Tendsto
      (fun k => (1 / isingFermionicGhostCoefficient) * layerRate k)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul H.layer_tendsto
  have hcommon : Tendsto common atTop (nhds 0) := by
    simpa [common, add_assoc] using (H.boundary_tendsto.add hbulk).add hlayer
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa [upper] using
      ((hcommon.add hvertexEndpoint_tendsto).add
        hfaceEndpoint_tendsto).add hmismatch_tendsto
  intro eta heta
  have heventually : ∀ᶠ k in atTop, dist (upper k) 0 < eta :=
    (Metric.tendsto_nhds.1 hupper) eta heta
  filter_upwards [heventually] with k hk
  intro e hsafe
  have hcommon_nonneg : 0 <= common k := by
    dsimp only [common]
    exact add_nonneg
      (add_nonneg (H.boundary_nonneg k)
        (mul_nonneg vertexBarrierGrowthConstant_nonneg
          (mul_nonneg (H.bulk_nonneg k) (sq_nonneg _))))
      (mul_nonneg
        (div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        (H.layer_nonneg k))
  have hupper_nonneg : 0 <= upper k := by
    dsimp only [upper]
    exact add_nonneg
      (add_nonneg
        (add_nonneg hcommon_nonneg
          (mul_nonneg (H.endpoint_nonneg k) (hvertexWeight_nonneg k)))
        (mul_nonneg (H.endpoint_nonneg k) (hfaceWeight_nonneg k)))
      (hmismatch_nonneg k)
  have hk' : upper k < eta := by
    simpa [Real.dist_eq, abs_of_nonneg hupper_nonneg] using hk
  let x := fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e
  let c := fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e
  have hv := H.vertex_error_le k x (hsafeVertex k e hsafe)
  have hvBarrier := vertexExplicitPoissonBarrierBound_le_growth
    (N k) (hN k)
  have hv' : |vertexDirichlet (N k) (hN k) (some x) -
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
        upper k := by
    calc
      _ <= boundaryRate k +
          bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) +
          layerRate k * vertexGhostLayerBarrier (N k) (some x) +
          endpointRate k *
            vertexMarkedEndpointBarrier (N k) (radius k) (some x) := hv
      _ <= boundaryRate k +
          bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) +
          endpointRate k * vertexEndpointWeight k := by
        gcongr
        · exact H.bulk_nonneg k
        · exact (vertexExplicitPoissonBarrier_le_bound (N k) (some x)).trans
            hvBarrier
        · exact H.layer_nonneg k
        · exact vertexGhostLayerBarrier_le (N k) (some x)
        · exact H.endpoint_nonneg k
        · exact hvertexWeight k e hsafe
      _ <= upper k := by
        dsimp only [upper, common]
        have hf : 0 <= endpointRate k * faceEndpointWeight k :=
          mul_nonneg (H.endpoint_nonneg k) (hfaceWeight_nonneg k)
        have hm : 0 <= mismatchRate k := hmismatch_nonneg k
        nlinarith
  have hf := H.face_error_le k c (hsafeFace k e hsafe)
  have hfBarrier : faceExplicitPoissonBarrierBound (N k) <=
      vertexBarrierGrowthConstant * (N k : Real) ^ 2 := by
    calc
      faceExplicitPoissonBarrierBound (N k) =
          (1 / 2 : Real) * (N k : Real) ^ 2 := by
        unfold faceExplicitPoissonBarrierBound
        ring
      _ <= vertexBarrierGrowthConstant * (N k : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
          (sq_nonneg _)
  have hfOwn : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
        common k + endpointRate k * faceEndpointWeight k := by
    calc
      _ <= boundaryRate k +
          bulkRate k * faceExplicitPoissonBarrier (N k) (some c) +
          layerRate k * faceGhostLayerBarrier (N k) (some c) +
          endpointRate k *
            faceMarkedEndpointBarrier (N k) (radius k) (some c) := hf
      _ <= boundaryRate k +
          bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) +
          endpointRate k * faceEndpointWeight k := by
        gcongr
        · exact H.bulk_nonneg k
        · exact (faceExplicitPoissonBarrier_le_bound (N k) (some c)).trans
            hfBarrier
        · exact H.layer_nonneg k
        · exact faceGhostLayerBarrier_le (N k) (some c)
        · exact H.endpoint_nonneg k
        · exact hfaceWeight k e hsafe
      _ = _ := by
        dsimp only [common]
        ring
  have hmis := hmismatch k e hsafe
  have hf' : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
        upper k := by
    rw [show faceDirichlet (N k) (hN k) (some c) -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im =
      (faceDirichlet (N k) (hN k) (some c) -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im) +
      ((Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im) by ring]
    calc
      |_ + _| <= |faceDirichlet (N k) (hN k) (some c) -
          (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| +
        |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im -
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| :=
            abs_add_le _ _
      _ <= (common k + endpointRate k * faceEndpointWeight k) +
          mismatchRate k := add_le_add hfOwn hmis
      _ <= upper k := by
        dsimp only [upper]
        have hvw : 0 <= endpointRate k * vertexEndpointWeight k :=
          mul_nonneg (H.endpoint_nonneg k) (hvertexWeight_nonneg k)
        nlinarith
  have hphysical := physicalIncidence_close_of_dirichlet_close
    (N k) (hN k) e
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im
    (upper k) hv' hf'
  exact ⟨hphysical.1.trans_lt hk', hphysical.2.trans_lt hk'⟩


theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_polynomial
    {Phi : Complex -> Complex}
    {mesh boundaryRate bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi mesh isingFermionicPolynomialRadius boundaryRate bulkRate layerRate
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
    (mismatchRate : Nat -> Real)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hmismatch : forall k e, PhysicalPolynomialEndpointSafe k e ->
      |(Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence
            (isingFermionicPolynomialSide k)
            (isingFermionicPolynomialSide_pos k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint
            (isingFermionicPolynomialSide k)
            (isingFermionicPolynomialSide_pos k) e))).im| <=
          mismatchRate k)
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k),
        PhysicalPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta := by
  apply H.primitive_convergence_away PhysicalPolynomialEndpointSafe
    vertexEndpointPolynomialBound faceEndpointPolynomialBound mismatchRate
  · exact vertexEndpointPolynomialBound_nonneg
  · exact faceEndpointPolynomialBound_nonneg
  · exact hmismatch_nonneg
  · intro k e hsafe
    exact hsafe.vertexNotFixed
  · intro k e hsafe
    exact hsafe.faceNotFixed
  · intro k e hsafe
    simpa [isingFermionicPolynomialSide,
      isingFermionicPolynomialRadius] using
      vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        k (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
        hsafe.vertexNotFixed hsafe.vertexRight hsafe.vertexBottom
        hsafe.vertexTop hsafe.vertexHalf
  · intro k e hsafe
    simpa [isingFermionicPolynomialSide,
      isingFermionicPolynomialRadius] using
      faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        k (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
        hsafe.faceNotFixed hsafe.faceHalf
  · exact hmismatch
  · simpa using tendsto_const_nhds.mul tendsto_vertexEndpointPolynomialBound
  · simpa using tendsto_const_nhds.mul tendsto_faceEndpointPolynomialBound
  · exact hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
