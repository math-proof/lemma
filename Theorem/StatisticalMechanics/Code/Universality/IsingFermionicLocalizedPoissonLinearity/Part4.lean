/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part3


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexMarkedEndpointBarrier_eq_sum_point (n radius : Nat) :
    vertexMarkedEndpointBarrier n radius =
      ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius),
        isingFiniteWeightedPointPoissonBarrier
          (vertexGhostGraph n) (vertexGhostConductance n)
          (vertexDirichletBoundary n)
          (vertexGhostConductance_nonneg n)
          (vertexGhostConductance_pos_of_adj n)
          (vertexGhost_reaches_boundary n) z := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)


theorem faceMarkedEndpointBarrier_eq_sum_point (n radius : Nat) :
    faceMarkedEndpointBarrier n radius =
      ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius),
        isingFiniteWeightedPointPoissonBarrier
          (faceGhostGraph n) (faceGhostConductance n)
          (faceDirichletBoundary n)
          (faceGhostConductance_nonneg n)
          (faceGhostConductance_pos_of_adj n)
          (faceGhost_reaches_boundary n) z := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)


theorem vertexMarkedEndpointBarrier_le_card_mul_reciprocal
    (n radius : Nat) (x : Option (FKIsingSquareFullVertexNode n))
    (hx : Not (vertexDirichletBoundary n x)) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) ->
      vertexPointPoissonBarrier n x z <= B) :
    vertexMarkedEndpointBarrier n radius x <=
      (isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary n)
        (vertexMarkedEndpointLayer n radius)).card * B := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
    (isingFiniteGhostConductance_comm _ _) x hx B hpoint


theorem faceMarkedEndpointBarrier_le_card_mul_reciprocal
    (n radius : Nat) (x : Option (FKIsingSquareFullFaceNode n))
    (hx : Not (faceDirichletBoundary n x)) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius) ->
      facePointPoissonBarrier n x z <= B) :
    faceMarkedEndpointBarrier n radius x <=
      (isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary n)
        (faceMarkedEndpointLayer n radius)).card * B := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
    (isingFiniteGhostConductance_comm _ _) x hx B hpoint


theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_of_pointGreen
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat} {bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      N hN Phi mesh radius bulkRate layerRate endpointRate)
    (safe : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
    (vertexGreenBound faceGreenBound mismatchRate : Nat -> Real)
    (hvertexGreen_nonneg : forall k, 0 <= vertexGreenBound k)
    (hfaceGreen_nonneg : forall k, 0 <= faceGreenBound k)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hvertexInterior : forall k e, safe k e ->
      Not (vertexDirichletBoundary (N k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))))
    (hfaceInterior : forall k e, safe k e ->
      Not (faceDirichletBoundary (N k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))))
    (hvertexGreen : forall k e, safe k e -> forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary (N k))
        (vertexMarkedEndpointLayer (N k) (radius k)) ->
      vertexPointPoissonBarrier (N k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) z <=
          vertexGreenBound k)
    (hfaceGreen : forall k e, safe k e -> forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary (N k))
        (faceMarkedEndpointLayer (N k) (radius k)) ->
      facePointPoissonBarrier (N k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) z <=
          faceGreenBound k)
    (hmismatch : forall k e, safe k e ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <=
        mismatchRate k)
    (hvertexEndpoint_tendsto : Filter.Tendsto
      (fun k => endpointRate k *
        ((isingFiniteWeightedInteriorExceptionalSources
          (vertexDirichletBoundary (N k))
          (vertexMarkedEndpointLayer (N k) (radius k))).card *
            vertexGreenBound k))
      Filter.atTop (nhds 0))
    (hfaceEndpoint_tendsto : Filter.Tendsto
      (fun k => endpointRate k *
        ((isingFiniteWeightedInteriorExceptionalSources
          (faceDirichletBoundary (N k))
          (faceMarkedEndpointLayer (N k) (radius k))).card *
            faceGreenBound k))
      Filter.atTop (nhds 0))
    (hmismatch_tendsto : Filter.Tendsto mismatchRate Filter.atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in Filter.atTop,
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
  apply H.primitive_convergence_away safe
    (fun k =>
      (isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary (N k))
        (vertexMarkedEndpointLayer (N k) (radius k))).card *
          vertexGreenBound k)
    (fun k =>
      (isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary (N k))
        (faceMarkedEndpointLayer (N k) (radius k))).card *
          faceGreenBound k)
    mismatchRate
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _) (hvertexGreen_nonneg k)
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _) (hfaceGreen_nonneg k)
  · exact hmismatch_nonneg
  · intro k e hsafe
    apply vertexMarkedEndpointBarrier_le_card_mul_reciprocal
    · exact hvertexInterior k e hsafe
    · exact hvertexGreen k e hsafe
  · intro k e hsafe
    apply faceMarkedEndpointBarrier_le_card_mul_reciprocal
    · exact hfaceInterior k e hsafe
    · exact hfaceGreen k e hsafe
  · exact hmismatch
  · exact hvertexEndpoint_tendsto
  · exact hfaceEndpoint_tendsto
  · exact hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
