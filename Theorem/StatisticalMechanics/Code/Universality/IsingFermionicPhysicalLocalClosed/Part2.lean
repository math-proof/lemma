/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveBridge
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalLocalClosed


namespace StatMech.Universality

open Complex

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredFullMedialObservable_eq_south_add_north
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredFullMedialObservable n hn e =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) :=
  fkIsingSquareWired_fermionicObservable_opposite_sum n hn e


theorem fkIsingSquareWiredFullMedialObservable_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
        (fkIsingSquareWiredFullMedialObservable n hn e) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (e, s)) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareWiredPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn z
  have hsum : W + E = S + N := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareWired_fermionicObservable_opposite_sum n hn e
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


theorem fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (s : FKIsingMedialSide) :
    fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, s)) =
      Complex.normSq
        (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
          (fkIsingSquareWiredFullMedialObservable n hn e)) := by
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareWiredFullMedialObservable_projection]


theorem fkIsingSquareWired_normSq_full_eq_west_add_east_increment
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Complex.normSq (fkIsingSquareWiredFullMedialObservable n hn e) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) := by
  rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection,
    fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, -, -⟩
      rw [hW, hE]
      exact (isingProj_normSq_add_neg 1 _ (by norm_num)).symm
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, -, -⟩
      rw [hW, hE]
      convert (isingProj_normSq_add_neg (-Complex.I) _ (by norm_num)).symm using 1 <;>
        ring


theorem fkIsingSquareWired_normSq_full_eq_south_add_north_increment
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Complex.normSq (fkIsingSquareWiredFullMedialObservable n hn e) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south)) +
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
  rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection,
    fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨-, -, hS, hN⟩
      rw [hS, hN]
      exact (isingProj_normSq_add_neg Complex.I _ (by norm_num)).symm
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨-, -, hS, hN⟩
      rw [hS, hN]
      exact (isingProj_normSq_add_neg 1 _ (by norm_num)).symm

end
end StatMech.Universality
