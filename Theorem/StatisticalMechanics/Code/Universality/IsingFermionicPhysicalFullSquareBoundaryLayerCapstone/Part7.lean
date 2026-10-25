/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part6


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem fkIsingSquareRightBoundaryMedialObservable_projection_north
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-1) (fkIsingSquareRightBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k
  let N := D.fermionicObservable (.dart (e, .north))
  let W := D.fermionicObservable (.dart (e, .west))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
    fkIsingSquarePerimeterEdge_axis n .right k
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hN : (starRingEnd Complex) N = -N := by
    simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
  have hW : (starRingEnd Complex) W = -Complex.I * W := by
    simpa only [W, htW] using hline (.dart (e, .west))
  change isingProj (-1) (rightBoundaryProjectionReconstruction N W) = N
  exact rightBoundaryProjectionReconstruction_projection_north N W hN hW

theorem fkIsingSquareRightBoundaryMedialObservable_projection_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-Complex.I)
        (fkIsingSquareRightBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k, .west)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k
  let N := D.fermionicObservable (.dart (e, .north))
  let W := D.fermionicObservable (.dart (e, .west))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
    fkIsingSquarePerimeterEdge_axis n .right k
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hN : (starRingEnd Complex) N = -N := by
    simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
  have hW : (starRingEnd Complex) W = -Complex.I * W := by
    simpa only [W, htW] using hline (.dart (e, .west))
  change isingProj (-Complex.I)
      (rightBoundaryProjectionReconstruction N W) = W
  exact rightBoundaryProjectionReconstruction_projection_west N W hN hW


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
