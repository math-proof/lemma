/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part5


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryLayerInward_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) =
      match side with
      | .bottom => 1
      | .right => -Complex.I
      | .top => -1
      | .left => Complex.I := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).1
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).1
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).2.1
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).2.1


theorem fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq
    (side : FKIsingSquareBoundarySide) :
    fkIsingSquareBoundaryLayerNormal side * (1 + isingLambda⁻¹) ^ 2 =
      ((2 + Real.sqrt 2 : Real) : Complex) *
        match side with
        | .bottom => 1
        | .right => -Complex.I
        | .top => -1
        | .left => Complex.I := by
  have hbase : isingLambda * (1 + isingLambda⁻¹) ^ 2 =
      ((2 + Real.sqrt 2 : Real) : Complex) := by
    calc
      _ = isingLambda + 2 + isingLambda⁻¹ := by
        field_simp [isingLambda_ne]
        ring
      _ = _ := by rw [isingLambda_inv]; push_cast; ring
  have hinvSq : isingLambda⁻¹ ^ 2 = -Complex.I := by
    rw [inv_pow, isingLambda_sq]
    simp
  cases side with
  | bottom => simpa [fkIsingSquareBoundaryLayerNormal] using hbase
  | right =>
      simp only [fkIsingSquareBoundaryLayerNormal]
      calc
        isingLambda⁻¹ * (1 + isingLambda⁻¹) ^ 2 =
            isingLambda⁻¹ ^ 2 *
              (isingLambda * (1 + isingLambda⁻¹) ^ 2) := by
          field_simp [isingLambda_ne]
        _ = _ := by rw [hinvSq, hbase]; ring
  | top =>
      simp only [fkIsingSquareBoundaryLayerNormal]
      rw [neg_mul, hbase]
      ring
  | left =>
      simp only [fkIsingSquareBoundaryLayerNormal]
      calc
        -isingLambda⁻¹ * (1 + isingLambda⁻¹) ^ 2 =
            -(isingLambda⁻¹ ^ 2 *
              (isingLambda * (1 + isingLambda⁻¹) ^ 2)) := by
          field_simp [isingLambda_ne]
        _ = _ := by rw [hinvSq, hbase]; ring


theorem fkIsingSquareBoundaryLayer_windingPhase_sq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
        omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase
        omega z ^ 2 =
      fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
  change (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (fkIsingSquareClosePerimeter n omega) z ^ 2 = _
  apply fkIsingSquareWired_windingPhase_sq n hn
  simpa [fkIsingSquareBoundaryRestrictedDobrushinDomain] using hz


theorem fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    ∃ t : Real, 0 <= t ∧
      fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerInwardSide side)) *
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n side k,
              fkIsingSquareBoundaryLayerInwardSide side))) ^ 2 =
        (t : Complex) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  apply D.exists_nonnegative_boundary_square_of_phase_sq z
    (fkIsingSquareWiredDirectedTangent n hn z)
    (fkIsingSquareWiredDirectedPhase n hn z) 1
  · intro omega hz
    exact fkIsingSquareBoundaryLayer_windingPhase_sq n hn omega z hz
  · exact zero_le_one
  · exact fkIsingSquareWiredDirectedTangent_mul_phase_sq n hn z


theorem fkIsingSquareBoundaryLayerVertexFermion_exists_nonnegative_square
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    ∃ t : Real, 0 <= t ∧
      fkIsingSquareBoundaryLayerNormal side *
          fkIsingSquareBoundaryLayerVertexFermion n hn side k ^ 2 =
        (t : Complex) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let c := isingFermionicBoundaryVertexNormalization
  obtain ⟨u, hu, hF⟩ :=
    fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square
      n hn side k
  have hnormal : fkIsingSquareBoundaryLayerNormal side *
        (1 + isingLambda⁻¹) ^ 2 =
      ((2 + Real.sqrt 2 : Real) : Complex) *
        fkIsingSquareWiredDirectedTangent n hn z := by
    rw [fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq,
      fkIsingSquareBoundaryLayerInward_directedTangent]
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (c : Complex) * (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (c : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change (c : Complex) * (F + F * isingLambda⁻¹) = _
    ring
  refine ⟨c ^ 2 * (2 + Real.sqrt 2) * u,
    mul_nonneg (mul_nonneg (sq_nonneg c) (by positivity)) hu, ?_⟩
  rw [hvertex]
  calc
    fkIsingSquareBoundaryLayerNormal side *
          ((c : Complex) * (F * (1 + isingLambda⁻¹))) ^ 2 =
        (c : Complex) ^ 2 *
          (fkIsingSquareBoundaryLayerNormal side *
            (1 + isingLambda⁻¹) ^ 2) * F ^ 2 := by ring
    _ = (c : Complex) ^ 2 *
          (((2 + Real.sqrt 2 : Real) : Complex) *
            fkIsingSquareWiredDirectedTangent n hn z) * F ^ 2 := by
      rw [hnormal]
    _ = (c : Complex) ^ 2 *
          ((2 + Real.sqrt 2 : Real) : Complex) * (u : Complex) := by
      have hTF : fkIsingSquareWiredDirectedTangent n hn z * F ^ 2 =
          (u : Complex) := by
        simpa only [D, z, F] using hF
      rw [show (c : Complex) ^ 2 *
          (((2 + Real.sqrt 2 : Real) : Complex) *
            fkIsingSquareWiredDirectedTangent n hn z) * F ^ 2 =
        (c : Complex) ^ 2 * ((2 + Real.sqrt 2 : Real) : Complex) *
          (fkIsingSquareWiredDirectedTangent n hn z * F ^ 2) by ring,
        hTF]
    _ = ((c ^ 2 * (2 + Real.sqrt 2) * u : Real) : Complex) := by
      push_cast
      ring

theorem isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq :
    isingFermionicBoundaryVertexNormalization ^ 2 *
        (2 + Real.sqrt 2) =
      isingFermionicBoundaryVertexNormSqFactor := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hden : 2 + Real.sqrt 2 ≠ 0 := by positivity
  unfold isingFermionicBoundaryVertexNormalization
    isingFermionicBoundaryVertexNormSqFactor
  field_simp [hden]
  nlinarith

theorem isingLambda_inv_val :
    isingLambda⁻¹ = (1 - Complex.I) / (Real.sqrt 2 : Complex) := by
  have hsqrt : (Real.sqrt 2 : Complex) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2))
  rw [isingLambda_inv, isingLambda_val]
  field_simp [hsqrt_ne]
  rw [hsqrt]
  ring

theorem isingLambda_one_add_inv_normSq :
    Complex.normSq (1 + isingLambda⁻¹) = 2 + Real.sqrt 2 := by
  rw [isingLambda_inv_val]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2))
  simp [Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.normSq_ofReal, hsqrt_ne]
  field_simp [hsqrt_ne]
  nlinarith


theorem fkIsingSquareBoundaryLayerVertexFermion_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicBoundaryVertexNormSqFactor *
        Complex.normSq
          ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n side k,
                fkIsingSquareBoundaryLayerInwardSide side))) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let c := isingFermionicBoundaryVertexNormalization
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (c : Complex) * (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (c : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change (c : Complex) * (F + F * isingLambda⁻¹) = _
    ring
  rw [hvertex, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, isingLambda_one_add_inv_normSq]
  change (c * c) *
      (Complex.normSq F * (2 + Real.sqrt 2)) =
    isingFermionicBoundaryVertexNormSqFactor * Complex.normSq F
  rw [show c * c = c ^ 2 by ring]
  calc
    c ^ 2 * (Complex.normSq F * (2 + Real.sqrt 2)) =
        (c ^ 2 * (2 + Real.sqrt 2)) * Complex.normSq F := by ring
    _ = _ := by
      rw [isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq]


end
end StatMech.Universality
