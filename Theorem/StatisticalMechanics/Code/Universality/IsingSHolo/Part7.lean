/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo.Part7


namespace StatMech.Universality

open Complex


theorem isingContour_eq_combination (D : IsingMedialVertex) (v d : ℂ)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
    isingContour (isingObservable D v d) (isingFace v d)
      = (Complex.I - 1) * d
          * (D.edgeObs 0 - D.edgeObs 1 + Complex.I * D.edgeObs 3 - Complex.I * D.edgeObs 2) := by
  rw [isingContour_expand]
  obtain ⟨e1, e2, e3, e4⟩ := isingFace_edges v d
  
  have h0 : isingObservable D v d ((isingFace v d 0 + isingFace v d 1) / 2) = D.edgeObs 0 := by
    unfold isingObservable; rw [if_pos rfl]
  have h1 : isingObservable D v d ((isingFace v d 1 + isingFace v d 2) / 2) = D.edgeObs 3 := by
    unfold isingObservable; rw [if_neg hpq.symm, if_pos rfl]
  have h2 : isingObservable D v d ((isingFace v d 2 + isingFace v d 3) / 2) = D.edgeObs 1 := by
    unfold isingObservable; rw [if_neg hpr.symm, if_neg hqr.symm, if_pos rfl]
  have h3 : isingObservable D v d ((isingFace v d 3 + isingFace v d 0) / 2) = D.edgeObs 2 := by
    unfold isingObservable; rw [if_neg hps.symm, if_neg hqs.symm, if_neg hrs.symm, if_pos rfl]
  rw [h0, h1, h2, h3, e1, e2, e3, e4]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  
  
  linear_combination (-(d * D.edgeObs 3 - d * D.edgeObs 2)) * hI


theorem ising_sholo_face_relation (D : IsingMedialVertex) (v d : ℂ)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
    isingContour (isingObservable D v d) (isingFace v d) = 0 := by
  rw [isingContour_eq_combination D v d hpq hpr hps hqr hqs hrs, D.contourCombination_zero,
      mul_zero]


theorem ising_sholo_closedContour
    {ι : Type*} (faces : Finset ι) (data : ι → IsingMedialVertex) (geo : ι → ℂ × ℂ)
    (hvanish : ∀ i ∈ faces,
      isingContour (isingObservable (data i) (geo i).1 (geo i).2)
        (isingFace (geo i).1 (geo i).2) = 0) :
    ∑ i ∈ faces,
      isingContour (isingObservable (data i) (geo i).1 (geo i).2)
        (isingFace (geo i).1 (geo i).2) = 0 :=
  Finset.sum_eq_zero hvanish


end StatMech.Universality
