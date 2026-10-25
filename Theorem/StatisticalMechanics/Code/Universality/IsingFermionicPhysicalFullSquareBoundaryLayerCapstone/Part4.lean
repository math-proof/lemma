/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem bottomMissingSouthProjectionReconstruction_projection_east
    (east west : Complex)
    (heast : (starRingEnd Complex) east = Complex.I * east)
    (hwest : (starRingEnd Complex) west = -west) :
    isingProj Complex.I
        (bottomMissingSouthProjectionReconstruction east west) = east := by
  unfold bottomMissingSouthProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one,
    Complex.conj_I, heast, hwest]
  norm_num
  ring_nf
  have hI2 : Complex.I ^ 2 = -1 := by norm_num [Complex.I_sq]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, hI2]
    ring
  rw [hI2, hI3]
  ring

theorem bottomMissingSouthProjectionReconstruction_projection_west
    (east west : Complex)
    (heast : (starRingEnd Complex) east = Complex.I * east)
    (hwest : (starRingEnd Complex) west = -west) :
    isingProj (-1)
        (bottomMissingSouthProjectionReconstruction east west) = west := by
  unfold bottomMissingSouthProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one, map_neg,
    heast, hwest]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
  ring

theorem isingProj_I_conj_line (z : Complex) :
    (starRingEnd Complex) (isingProj Complex.I z) =
      Complex.I * isingProj Complex.I z := by
  unfold isingProj
  simp only [map_mul, map_add, map_one, Complex.conj_I, map_neg,
    starRingEnd_apply]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
  ring

theorem isingProj_negOne_conj_line (z : Complex) :
    (starRingEnd Complex) (isingProj (-1) z) =
      -isingProj (-1) z := by
  unfold isingProj
  simp only [map_mul, map_add, map_one, map_neg, starRingEnd_apply]
  norm_num
  ring

theorem boundaryLayerEndpoint_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda ^ 2 := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]


theorem boundaryVertexFermion_projection_inward
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerInwardSide side)))
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj t _ = F
  rw [hvertex]
  apply boundaryVertexProjection_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerInward_directedTangent]
  cases side <;> norm_num


theorem boundaryVertexFermion_projection_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerEndpointSide side)))
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  rw [boundaryLayerEndpoint_directedTangent]
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
  change isingProj (t * isingLambda ^ 2) _ = F * isingLambda⁻¹
  rw [hvertex]
  apply boundaryVertexProjection_endpoint_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerInward_directedTangent]
  cases side <;> norm_num


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
