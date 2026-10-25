/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part7


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem fkIsingSquareTopBoundaryMedialObservable_projection_south
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj Complex.I (fkIsingSquareTopBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k, .south)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k
  let S := D.fermionicObservable (.dart (e, .south))
  let E := D.fermionicObservable (.dart (e, .east))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .top k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨_, htE, htS, _⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hS : (starRingEnd Complex) S = Complex.I * S := by
    simpa only [S, htS] using hline (.dart (e, .south))
  have hE : (starRingEnd Complex) E = -E := by
    simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
  change isingProj Complex.I
      (bottomMissingSouthProjectionReconstruction S E) = S
  exact bottomMissingSouthProjectionReconstruction_projection_east S E hS hE

theorem fkIsingSquareTopBoundaryMedialObservable_projection_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-1) (fkIsingSquareTopBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k, .east)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k
  let S := D.fermionicObservable (.dart (e, .south))
  let E := D.fermionicObservable (.dart (e, .east))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .top k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨_, htE, htS, _⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hS : (starRingEnd Complex) S = Complex.I * S := by
    simpa only [S, htS] using hline (.dart (e, .south))
  have hE : (starRingEnd Complex) E = -E := by
    simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
  change isingProj (-1)
      (bottomMissingSouthProjectionReconstruction S E) = E
  exact bottomMissingSouthProjectionReconstruction_projection_west S E hS hE


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
