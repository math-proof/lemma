/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStripCauchyFourthOrder.Part2
open Metric


namespace StatMech.Universality

open Metric

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def
    PhysicalEndpointVariableFourthOrderBulkData.ofUnitStripCenteredBalls
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (d : Nat -> Real) (hd : forall k, 0 < d k)
    (hmesh : forall k, 2 * |mesh k| < d k / 2)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      DifferentiableOn Complex Phi (ball z (d k)) /\
        (forall w, w ∈ ball z (d k) ->
          0 <= (Phi w).im /\ (Phi w).im <= 1))
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      DifferentiableOn Complex Phi (ball z (d k)) /\
        (forall w, w ∈ ball z (d k) ->
          0 <= (Phi w).im /\ (Phi w).im <= 1)) :
    PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius where
  boundOne k := 4 * (unitStripHalfBallFourthTensorBound (d k) : Real)
  boundTwo k := 4 * (unitStripHalfBallFourthTensorBound (d k) : Real)
  boundSum_nonneg k := by positivity
  vertex k x hfixed hghost hendpoint := by
    obtain ⟨hPhi, hrange⟩ := hvertex k x hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
      (hd k) (hmesh k) hPhi hrange
  face k c hfixed hghost hendpoint := by
    obtain ⟨hPhi, hrange⟩ := hface k c hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofUnitStripOnCenteredBall
      (hd k) (hmesh k) hPhi hrange

end FKIsingSquareBoundaryLayerCoordinateOneForm
end StatMech.Universality
