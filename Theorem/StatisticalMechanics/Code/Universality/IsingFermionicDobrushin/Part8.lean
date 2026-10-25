/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part9
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


namespace LocalSwitchingTable

variable (T : D.LocalSwitchingTable)


theorem localFaceObservable_sideValues (v d : Complex)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2) :
    localFaceObservable D T v d
        ((isingFace v d 0 + isingFace v d 1) / 2) =
        D.fermionicObservable (T.edges 0) ∧
      localFaceObservable D T v d
        ((isingFace v d 1 + isingFace v d 2) / 2) =
        D.fermionicObservable (T.edges 3) ∧
      localFaceObservable D T v d
        ((isingFace v d 2 + isingFace v d 3) / 2) =
        D.fermionicObservable (T.edges 1) ∧
      localFaceObservable D T v d
        ((isingFace v d 3 + isingFace v d 0) / 2) =
        D.fermionicObservable (T.edges 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold localFaceObservable isingObservable
    rw [if_pos rfl, ← fermionicObservable_eq_medialVertex_edgeObs D T 0]
  · unfold localFaceObservable isingObservable
    rw [if_neg hpq.symm, if_pos rfl,
      ← fermionicObservable_eq_medialVertex_edgeObs D T 3]
  · unfold localFaceObservable isingObservable
    rw [if_neg hpr.symm, if_neg hqr.symm, if_pos rfl,
      ← fermionicObservable_eq_medialVertex_edgeObs D T 1]
  · unfold localFaceObservable isingObservable
    rw [if_neg hps.symm, if_neg hqs.symm, if_neg hrs.symm, if_pos rfl,
      ← fermionicObservable_eq_medialVertex_edgeObs D T 2]


theorem localFaceObservable_contour_zero (v d : Complex)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2) :
    isingContour (localFaceObservable D T v d) (isingFace v d) = 0 := by
  exact ising_sholo_face_relation (medialVertex D T) v d
    hpq hpr hps hqr hqs hrs


theorem fermionicObservable_sHolo_relation :
    D.fermionicObservable (T.edges 0) + D.fermionicObservable (T.edges 1) =
      D.fermionicObservable (T.edges 2) + D.fermionicObservable (T.edges 3) := by
  have hpoint (omega : ConfigSpace (Sym2 P.V)) :
      (D.fermionicSummand omega (T.edges 0) +
          D.fermionicSummand (T.toggle omega) (T.edges 0)) +
        (D.fermionicSummand omega (T.edges 1) +
          D.fermionicSummand (T.toggle omega) (T.edges 1)) =
      (D.fermionicSummand omega (T.edges 2) +
          D.fermionicSummand (T.toggle omega) (T.edges 2)) +
        (D.fermionicSummand omega (T.edges 3) +
          D.fermionicSummand (T.toggle omega) (T.edges 3)) := by
    obtain ⟨X, hX⟩ := T.pairedContribution omega
    rw [hX 0, hX 1, hX 2, hX 3]
    exact isingF_sHolo_relation X
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 0) +
            D.fermionicSummand (T.toggle omega) (T.edges 0)) +
          (D.fermionicSummand omega (T.edges 1) +
            D.fermionicSummand (T.toggle omega) (T.edges 1)))) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 2) +
            D.fermionicSummand (T.toggle omega) (T.edges 2)) +
          (D.fermionicSummand omega (T.edges 3) +
            D.fermionicSummand (T.toggle omega) (T.edges 3))) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact hpoint omega
  simp only [Finset.sum_add_distrib] at hsum
  rw [T.sum_toggle D 0, T.sum_toggle D 1,
    T.sum_toggle D 2, T.sum_toggle D 3] at hsum
  unfold fermionicObservable
  linear_combination (1 / 2 : Complex) * hsum


theorem fermionicObservable_contourCombination_zero :
    D.fermionicObservable (T.edges 0) - D.fermionicObservable (T.edges 1) +
        Complex.I * D.fermionicObservable (T.edges 3) -
          Complex.I * D.fermionicObservable (T.edges 2) = 0 := by
  have hpoint (omega : ConfigSpace (Sym2 P.V)) :
      (D.fermionicSummand omega (T.edges 0) +
          D.fermionicSummand (T.toggle omega) (T.edges 0)) -
        (D.fermionicSummand omega (T.edges 1) +
          D.fermionicSummand (T.toggle omega) (T.edges 1)) +
        Complex.I * (D.fermionicSummand omega (T.edges 3) +
          D.fermionicSummand (T.toggle omega) (T.edges 3)) -
        Complex.I * (D.fermionicSummand omega (T.edges 2) +
          D.fermionicSummand (T.toggle omega) (T.edges 2)) = 0 := by
    obtain ⟨X, hX⟩ := T.pairedContribution omega
    rw [hX 0, hX 1, hX 2, hX 3]
    exact (IsingMedialVertex.mk X).contourCombination_zero
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 0) +
            D.fermionicSummand (T.toggle omega) (T.edges 0)) -
          (D.fermionicSummand omega (T.edges 1) +
            D.fermionicSummand (T.toggle omega) (T.edges 1)) +
          Complex.I * (D.fermionicSummand omega (T.edges 3) +
            D.fermionicSummand (T.toggle omega) (T.edges 3)) -
          Complex.I * (D.fermionicSummand omega (T.edges 2) +
            D.fermionicSummand (T.toggle omega) (T.edges 2)))) =
      ∑ _omega : ConfigSpace (Sym2 P.V), (0 : Complex) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact hpoint omega
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const_zero] at hsum
  rw [T.sum_toggle D 0, T.sum_toggle D 1,
    T.sum_toggle D 2, T.sum_toggle D 3] at hsum
  unfold fermionicObservable
  linear_combination (1 / 2 : Complex) * hsum

end LocalSwitchingTable
end FKIsingDobrushinDomain
end
end StatMech.Universality
