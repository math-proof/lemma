/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part3


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryFullMedialObservable_eq_south_add_north
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    fkIsingSquareBoundaryFullMedialObservable n hn e =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) :=
  fkIsingSquareBoundary_fermionicObservable_opposite_sum n hn e he

theorem fkIsingSquareBoundaryFullMedialObservable_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
        (fkIsingSquareBoundaryFullMedialObservable n hn e) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (e, s)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hsum : W + E = S + N := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareBoundary_fermionicObservable_opposite_sum n hn e he
  change isingProj _ (W + E) = _
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨htW, htE, htS, htN⟩
      cases s
      · rw [htW]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [W, htW, one_mul] using hline (.dart (e, .west))
        · simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
      · rw [htE, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [E, htE] using hline (.dart (e, .east))
        · simpa only [W, htW, one_mul, neg_neg, neg_one_mul] using
            hline (.dart (e, .west))
      · rw [htS, hsum]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [S, htS] using hline (.dart (e, .south))
        · simpa only [N, htN, neg_mul, neg_neg] using hline (.dart (e, .north))
      · rw [htN, hsum, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [N, htN, neg_mul] using hline (.dart (e, .north))
        · simpa only [S, htS, neg_neg] using hline (.dart (e, .south))
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨htW, htE, htS, htN⟩
      cases s
      · rw [htW]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [W, htW, neg_mul] using hline (.dart (e, .west))
        · simpa only [E, htE, neg_neg] using hline (.dart (e, .east))
      · rw [htE, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [E, htE] using hline (.dart (e, .east))
        · simpa only [W, htW, neg_mul, neg_neg] using hline (.dart (e, .west))
      · rw [htS, hsum]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [S, htS, one_mul] using hline (.dart (e, .south))
        · simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
      · rw [htN, hsum, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
        · simpa only [S, htS, one_mul, neg_neg, neg_one_mul] using
            hline (.dart (e, .south))

theorem fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (s : FKIsingMedialSide) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, s)) =
      Complex.normSq
        (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
          (fkIsingSquareBoundaryFullMedialObservable n hn e)) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareBoundaryFullMedialObservable_projection n hn e he s]


theorem fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    (n : Nat) (hn : 0 < n) (d : FKIsingSquareInteriorRadialDart n)
    (hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d.1) := by
  have hturn :=
    fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq
      n hn d hcode
  have hphase : fkIsingSquareWiredBondPhase n hn d.1 = 1 := by
    unfold fkIsingSquareWiredBondPhase
    rw [show fkIsingSquareWiredBondTurn n hn d.1
        (fkIsingSquareWiredBondMate n hn d.1) = 0 by exact hturn]
    norm_num
  calc
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d).1) := by
      rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
    _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.bond d.1) *
        fkIsingSquareWiredBondPhase n hn d.1 := by
      change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.bond (fkIsingSquareWiredBondMate n hn d.1)) = _
      exact fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
        n hn d.1
          (fkIsingSquareInteriorRadialDart_ne_source n hn d)
          (fkIsingSquareInteriorRadialDart_ne_terminal n hn d)
    _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart d.1) := by
      rw [hphase, mul_one,
        fkIsingSquareBoundaryLayer_fermionicObservable_incidence]

end
end StatMech.Universality
