/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part4


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem fkIsingSquareBoundaryLayerComplementInward_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) =
      match side with
      | .bottom => -1
      | .right => Complex.I
      | .top => 1
      | .left => -Complex.I := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).2.1
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).2.1
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).1
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).1

theorem boundaryLayerComplementEndpoint_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda ^ 2 := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]

theorem complementBoundaryVertexFermion_projection_inward
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementInwardSide side)))
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj t _ = F
  rw [hvertex]
  apply boundaryVertexProjection_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerComplementInward_directedTangent]
  cases side <;> norm_num

theorem complementBoundaryVertexFermion_projection_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementEndpointSide side)))
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  rw [boundaryLayerComplementEndpoint_directedTangent]
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
  change isingProj (t * isingLambda ^ 2) _ = F * isingLambda⁻¹
  rw [hvertex]
  apply boundaryVertexProjection_endpoint_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerComplementInward_directedTangent]
  cases side <;> norm_num

theorem fkIsingSquareBoundaryLayerComplementVertexFermion_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      isingFermionicBoundaryVertexNormSqFactor *
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let F := D.fermionicObservable
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side))
  let c := isingFermionicBoundaryVertexNormalization
  have hvertex : fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k =
      (c : Complex) * (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (c : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
    change (c : Complex) * (F + F * isingLambda⁻¹) = _
    ring
  rw [hvertex, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, isingLambda_one_add_inv_normSq]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  change (c * c) * (Complex.normSq F * (2 + Real.sqrt 2)) =
    isingFermionicBoundaryVertexNormSqFactor * Complex.normSq F
  rw [show c * c = c ^ 2 by ring]
  calc
    c ^ 2 * (Complex.normSq F * (2 + Real.sqrt 2)) =
        (c ^ 2 * (2 + Real.sqrt 2)) * Complex.normSq F := by ring
    _ = _ := by
      rw [isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq]

theorem fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
  rw [fkIsingSquareBoundaryLayerComplementVertexFermion_normSq,
    <- mul_assoc,
    isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor]


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
