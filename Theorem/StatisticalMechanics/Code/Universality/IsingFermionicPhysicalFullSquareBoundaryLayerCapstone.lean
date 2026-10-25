/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryLayerInwardIncrement_le_one
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k <= 1 := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  have hnorm := D.norm_fermionicObservable_le_one z
  unfold fkIsingSquareBoundaryLayerInwardIncrement
  change Complex.normSq (D.fermionicObservable z) <= 1
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (D.fermionicObservable z)]

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

@[simp] theorem markedB_base (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
      (fkIsingSquareMarkedB n) = 0 := by
  unfold FKIsingSquareFullCoordinateOneForm.vertexPrimitive
  ring

theorem vertex_eq_of_common_face_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f)
    (hinc : fkIsingSquareBoundaryLayerRadialIncrement n hn e =
      fkIsingSquareBoundaryLayerRadialIncrement n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn f) := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn f
  rw [hface] at he
  linarith

theorem face_eq_of_common_vertex_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hvertex : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f)
    (hinc : fkIsingSquareBoundaryLayerRadialIncrement n hn e =
      fkIsingSquareBoundaryLayerRadialIncrement n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn f) := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn f
  rw [hvertex] at he
  linarith

theorem boundaryVertexProjection_algebra
    (F t : Complex)
    (hline : (starRingEnd Complex) F = t * F)
    (ht : Complex.normSq t = 1) :
    isingProj t
        ((isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹))) = F := by
  have hct : (starRingEnd Complex) t * t = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ht]
    norm_num
  have hlamConj : (starRingEnd Complex) isingLambda = isingLambda⁻¹ := by
    rw [isingLambda_inv_val, isingLambda_val]
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im]
  unfold isingProj
  rw [map_mul, map_mul, map_add, map_one, map_inv₀, hline,
    hlamConj, inv_inv]
  rw [show (starRingEnd Complex)
      (isingFermionicBoundaryVertexNormalization : Complex) =
        isingFermionicBoundaryVertexNormalization by simp]
  have hcollapse : (starRingEnd Complex) t *
      ((isingFermionicBoundaryVertexNormalization : Complex) *
        (t * F * (1 + isingLambda))) =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        F * (1 + isingLambda) := by
    calc
      _ = (isingFermionicBoundaryVertexNormalization : Complex) *
          (((starRingEnd Complex) t * t) * F) *
            (1 + isingLambda) := by ring
      _ = _ := by rw [hct]; ring
  rw [hcollapse]
  rw [isingLambda_inv]
  have hden : (2 + Real.sqrt 2 : Real) ≠ 0 := by positivity
  have hdenC : ((2 + Real.sqrt 2 : Real) : Complex) ≠ 0 := by
    exact_mod_cast hden
  have hdenC' : (2 + (Real.sqrt 2 : Complex)) ≠ 0 := by
    simpa using hdenC
  unfold isingFermionicBoundaryVertexNormalization
  push_cast
  field_simp [hdenC']
  ring

theorem boundaryVertexProjection_endpoint_algebra
    (F t : Complex)
    (hline : (starRingEnd Complex) F = t * F)
    (ht : Complex.normSq t = 1) :
    isingProj (t * isingLambda ^ 2)
        ((isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹))) = F * isingLambda⁻¹ := by
  have hct : (starRingEnd Complex) t * t = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ht]
    norm_num
  have hlamConj : (starRingEnd Complex) isingLambda = isingLambda⁻¹ := by
    rw [isingLambda_inv_val, isingLambda_val]
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im]
  unfold isingProj
  rw [map_mul, map_pow, map_mul, map_mul, map_add, map_one, map_inv₀,
    hline, hlamConj, inv_inv]
  rw [show (starRingEnd Complex)
      (isingFermionicBoundaryVertexNormalization : Complex) =
        isingFermionicBoundaryVertexNormalization by simp]
  have hcollapse : (starRingEnd Complex) t * (isingLambda⁻¹) ^ 2 *
      ((isingFermionicBoundaryVertexNormalization : Complex) *
        (t * F * (1 + isingLambda))) =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        ((isingLambda⁻¹) ^ 2 * F) * (1 + isingLambda) := by
    calc
      _ = (isingFermionicBoundaryVertexNormalization : Complex) *
          ((isingLambda⁻¹) ^ 2 *
            (((starRingEnd Complex) t * t) * F)) *
              (1 + isingLambda) := by ring
      _ = _ := by rw [hct]; ring
  rw [hcollapse]
  have hden : (2 + Real.sqrt 2 : Real) ≠ 0 := by positivity
  have hdenC : (2 + (Real.sqrt 2 : Complex)) ≠ 0 := by
    exact_mod_cast hden
  have hs : (Real.sqrt 2 : Complex) = isingLambda + isingLambda⁻¹ := by
    rw [isingLambda_inv]
    ring
  have hsum :
      1 + isingLambda⁻¹ + (isingLambda⁻¹) ^ 2 * (1 + isingLambda) =
        (2 + (Real.sqrt 2 : Complex)) * isingLambda⁻¹ := by
    rw [hs]
    field_simp [isingLambda_ne]
    ring
  calc
    _ = ((1 / 2 : Complex) *
          (isingFermionicBoundaryVertexNormalization : Complex) *
            (1 + isingLambda⁻¹ +
              (isingLambda⁻¹) ^ 2 * (1 + isingLambda))) * F := by ring
    _ = ((1 / 2 : Complex) *
          (isingFermionicBoundaryVertexNormalization : Complex) *
            ((2 + (Real.sqrt 2 : Complex)) * isingLambda⁻¹)) * F := by
      rw [hsum]
    _ = F * isingLambda⁻¹ := by
      unfold isingFermionicBoundaryVertexNormalization
      push_cast
      field_simp [hdenC]


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
