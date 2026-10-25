/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part5


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem fkIsingSquareBottomBoundaryMedialObservable_projection_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj 1 (fkIsingSquareBottomBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k, .west)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom k
  let W := D.fermionicObservable (.dart (e, .west))
  let N := D.fermionicObservable (.dart (e, .north))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .bottom k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hW : (starRingEnd Complex) W = W := by
    simpa only [W, htW, one_mul] using hline (.dart (e, .west))
  have hN : (starRingEnd Complex) N = -Complex.I * N := by
    simpa only [N, htN] using hline (.dart (e, .north))
  change isingProj 1 (bottomBoundaryProjectionReconstruction W N) = W
  exact bottomBoundaryProjectionReconstruction_projection_west W N hW hN

theorem fkIsingSquareBottomBoundaryMedialObservable_projection_north
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-Complex.I)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom k
  let W := D.fermionicObservable (.dart (e, .west))
  let N := D.fermionicObservable (.dart (e, .north))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .bottom k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hW : (starRingEnd Complex) W = W := by
    simpa only [W, htW, one_mul] using hline (.dart (e, .west))
  have hN : (starRingEnd Complex) N = -Complex.I * N := by
    simpa only [N, htN] using hline (.dart (e, .north))
  change isingProj (-Complex.I)
      (bottomBoundaryProjectionReconstruction W N) = N
  exact bottomBoundaryProjectionReconstruction_projection_north W N hW hN


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
