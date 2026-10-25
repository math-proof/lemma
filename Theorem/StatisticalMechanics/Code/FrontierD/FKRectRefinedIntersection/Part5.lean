/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectEven_add_self (k : Nat) : Even (k + k) :=
  ⟨k, rfl⟩

theorem fkRectNotEven_add_self_add_one (k : Nat) :
    ¬ Even (k + k + 1) := by
  intro h
  obtain ⟨m, hm⟩ := h
  omega

theorem fkRectEven_two_mul (k : Nat) : Even (2 * k) :=
  ⟨k, by omega⟩

theorem fkRectNotEven_two_mul_add_one (k : Nat) :
    ¬ Even (2 * k + 1) := by
  intro h
  obtain ⟨m, hm⟩ := h
  omega

theorem fkRectEven_two_mul_add_two (k : Nat) :
    Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩

theorem fkRectNotEven_height_pred (R : FKRectTorus) :
    ¬ Even (R.height - 1) := by
  intro hpred
  obtain ⟨m, hm⟩ := hpred
  obtain ⟨n, hn⟩ := R.height_even
  have hpos := R.height_pos
  omega

theorem fkRectWidth_ne_two (R : FKRectTorus) : R.width ≠ 2 :=
  ne_of_gt R.width_gt_two

theorem fkRectHeight_ne_two (R : FKRectTorus) : R.height ≠ 2 :=
  ne_of_gt R.height_gt_two

theorem fkRectInt_add_self_ediv_two (k : Nat) :
    ((k : Int) + k) / 2 = k := by omega

theorem fkRectInt_add_self_add_one_ediv_two (k : Nat) :
    ((k : Int) + k + 1) / 2 = k := by omega

theorem fkRectInt_add_self_add_two_ediv_two (k : Nat) :
    ((k : Int) + k + 1 + 1) / 2 = k + 1 := by omega

theorem fkRectInt_two_mul_add_one_ediv_two (k : Nat) :
    (2 * (k : Int) + 1) / 2 = k := by omega

theorem fkRectInt_two_mul_add_two_ediv_two (k : Nat) :
    (2 * (k : Int) + 1 + 1) / 2 = k + 1 := by omega

theorem fkRectInt_one_add_mul_two_ediv_two (k : Nat) :
    (1 + (k : Int) * 2) / 2 = k := by omega

theorem fkRectInt_two_add_mul_two_ediv_two (k : Nat) :
    (2 + (k : Int) * 2) / 2 = k + 1 := by omega

theorem fkRectInt_three_add_mul_two_ediv_two (k : Nat) :
    (3 + (k : Int) * 2) / 2 = k + 1 := by omega

theorem fkRectInt_neg_one_add_mul_two_ediv_two (k : Nat) :
    (-1 + (k : Int) * 2) / 2 = (k : Int) - 1 := by omega

theorem fkRectInt_neg_two_add_mul_two_ediv_two (k : Nat) :
    (-2 + (k : Int) * 2) / 2 = (k : Int) - 1 := by omega

theorem fkRectHeight_int_ediv_two (R : FKRectTorus) :
    (R.height : Int) / 2 = (R.height / 2 : Nat) := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  omega

theorem fkRectHeight_pred_int_ediv_two (R : FKRectTorus) :
    ((R.height - 1 : Nat) : Int) / 2 = (R.height / 2 : Nat) - 1 := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  have hsub : R.height - 1 + 1 = R.height :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt R.height_pos))
  omega

theorem fkRectHeight_pred_add_one_int_ediv_two
    (R : FKRectTorus) :
    (((R.height - 1 : Nat) : Int) + 1) / 2 =
      (R.height / 2 : Nat) := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  have hsub : R.height - 1 + 1 = R.height :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt R.height_pos))
  omega

theorem fkRectWidth_pred_int_cast (R : FKRectTorus) :
    ((R.width - 1 : Nat) : Int) = (R.width : Int) - 1 := by
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt R.width_pos))]
  norm_num

theorem fkRectHeight_pred_int_cast (R : FKRectTorus) :
    ((R.height - 1 : Nat) : Int) = (R.height : Int) - 1 := by
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt R.height_pos))]
  norm_num

theorem fkRectHeight_int_sub_one_ediv_two (R : FKRectTorus) :
    ((R.height : Int) - 1) / 2 = (R.height / 2 : Nat) - 1 := by
  rw [← fkRectHeight_pred_int_cast]
  exact fkRectHeight_pred_int_ediv_two R

theorem fkRectHeight_int_sub_one_add_one_ediv_two
    (R : FKRectTorus) :
    (((R.height : Int) - 1) + 1) / 2 =
      (R.height / 2 : Nat) := by
  rw [← fkRectHeight_pred_int_cast]
  exact fkRectHeight_pred_add_one_int_ediv_two R

theorem fkRectNotEven_mul_two_sub_one (k : Nat) (hk : k ≠ 0) :
    ¬ Even (k * 2 - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  intro h
  obtain ⟨m, hm⟩ := h
  omega

theorem fkRectMulTwoSubOne_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    (((k * 2 - 1 : Nat) : Int)) / 2 = (k : Int) - 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  omega

theorem fkRectOneAddMulTwoSubOne_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    (1 + ((k * 2 - 1 : Nat) : Int)) / 2 = k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  omega

theorem fkRectFinPred_int_cast {n : Nat} (x : Fin n)
    (hx : x.val ≠ 0) :
    ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
  omega

theorem fkRectAddSelfSubOne_int_cast (k : Nat) (hk : k ≠ 0) :
    ((k + k - 1 : Nat) : Int) = (k : Int) + k - 1 := by
  omega

theorem fkRectAddSelfSubOne_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    ((k + k - 1 : Nat) : Int) / 2 = (k : Int) - 1 := by
  omega

theorem fkRectAddSelfSubOne_add_one_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    (((k + k - 1 : Nat) : Int) + 1) / 2 = k := by
  omega

theorem fkRectHeight_int_negOne_add_ediv_two (R : FKRectTorus) :
    (-1 + (R.height : Int)) / 2 = (R.height / 2 : Nat) - 1 := by
  convert fkRectHeight_int_sub_one_ediv_two R using 1 <;> ring

theorem fkRectHeight_int_negTwo_add_ediv_two (R : FKRectTorus) :
    (-2 + (R.height : Int)) / 2 = (R.height / 2 : Nat) - 1 := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  omega

theorem fkRectHeight_one_add_negOne_add_ediv_two
    (R : FKRectTorus) :
    (1 + (-1 + (R.height : Int))) / 2 =
      (R.height / 2 : Nat) := by
  convert fkRectHeight_int_sub_one_add_one_ediv_two R using 1 <;> ring

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in


theorem fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) :
    fkRectRefinedBondCenter (fkRectRefinedBoundaryCanonicalCenter R d)
        (fkMedialLocalMate pairing d).2 =
      ((fkRectRefinedBoundaryCanonicalCenter R
          (fkMedialBoundaryStep pairing d)).1 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamIncrement R pairing d)).1 +
          (fkRectRefinedBoundaryPrimalPotential R d).1 -
          (fkRectRefinedBoundaryPrimalPotential R
            (fkMedialBoundaryStep pairing d)).1,
        (fkRectRefinedBoundaryCanonicalCenter R
          (fkMedialBoundaryStep pairing d)).2 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamIncrement R pairing d)).2 +
          (fkRectRefinedBoundaryPrimalPotential R d).2 -
          (fkRectRefinedBoundaryPrimalPotential R
            (fkMedialBoundaryStep pairing d)).2) := by
  unfold fkRectRefinedBoundaryCanonicalCenter
    fkRectMedialBoundaryPrimalSeamIncrement
    fkRectRefinedBoundaryPrimalPotential
    fkRectRefinedBoundaryPrimalLift
  simp only [fkMedialBoundaryStep_apply]
  rw [fkRectTorusMedialEdgeEquiv_bondMate]
  rw [fkRectMedialDartPrimalLabel_bondMate]
  have hW1 : 1 ≠ R.width :=
    Nat.ne_of_lt (lt_trans Nat.one_lt_two R.width_gt_two)
  have hH1 : 1 ≠ R.height :=
    Nat.ne_of_lt (lt_trans Nat.one_lt_two R.height_gt_two)
  have hWgt := R.width_gt_two
  have hHgt := R.height_gt_two
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  have hWsub : R.width - 1 + 1 = R.width :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt R.width_pos))
  have hHsub : R.height - 1 + 1 = R.height :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt R.height_pos))
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases hp : pairing (fkRectMedialVertexOfEdge R (b, x, y)) <;>
    cases b <;> cases side <;>
    by_cases hy : Even y.val <;>
    by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0 <;>
    by_cases hxl : x.val + 1 = R.width <;>
    by_cases hyl : y.val + 1 = R.height
  all_goals try omega
  all_goals
    first
    | obtain ⟨k, hk⟩ := hy
    | obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
  all_goals
    simp_all only [fkRectMedialDartPrimalLabel, fkMedialLocalMate,
      fkMedialBondMate,
      fkRectMedialBondEdgeIndex,
      fkRectMedialWestPrimal, fkRectMedialEastPrimal,
      fkRectClosedPairingAtEdge, even_finitePeriodicSucc_iff,
      even_cyclicPred_iff, Nat.even_add_one,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge]
  all_goals simp_all
  all_goals by_cases hk0 : k = 0
  all_goals try omega
  all_goals
    simp_all only [fkRectRefinedBondCenter, fkRectRefinedSideOffset,
      fkRectRefinedPrimalEdgeCenter, fkRectLiftedIndexedEdgeEnds,
      fkRectSquareDeckTranslation,
      fkRectHorizontalSeamIncrement, fkRectVerticalSeamIncrement,
      fkRectSquareDevelopPoint, fkRectVertexSquarePoint,
      finitePeriodicSucc_val,
      fkRectCyclicPred_val,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge,
      fkRectWidth_ne_two, fkRectHeight_ne_two,
      hk0,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      true_and, and_true, false_and, and_false,
      Prod.fst, Prod.snd, Fin.val_mk]
  all_goals by_cases hk1 : k = 0
  all_goals try omega
  all_goals simp_all only [hk0, hk1]
  all_goals
    try simp only [hk0, hk1, fkRectEven_add_self,
      fkRectNotEven_add_self_add_one, fkRectEven_two_mul,
      fkRectNotEven_two_mul_add_one,
      fkRectEven_two_mul_add_two,
      fkRectNotEven_height_pred] at *
  all_goals
    first
    | (have hkpred := fkRectNotEven_mul_two_sub_one k hk1
       simp only [hkpred] at *)
    | skip
  all_goals
    try simp only [hk0, hk1, fkRectInt_add_self_ediv_two,
      fkRectInt_add_self_add_one_ediv_two,
      fkRectInt_add_self_add_two_ediv_two,
      fkRectInt_two_mul_add_one_ediv_two,
      fkRectInt_two_mul_add_two_ediv_two,
      fkRectHeight_int_ediv_two,
      fkRectHeight_pred_int_ediv_two,
      fkRectHeight_pred_add_one_int_ediv_two,
      fkRectWidth_pred_int_cast,
      fkRectHeight_pred_int_cast,
      fkRectHeight_int_sub_one_ediv_two,
      fkRectHeight_int_sub_one_add_one_ediv_two,
      fkRectHeight_int_negOne_add_ediv_two,
      fkRectHeight_one_add_negOne_add_ediv_two] at *
  all_goals
    first
    | (have hkdiv := fkRectMulTwoSubOne_int_ediv_two k hk1
       have hkdiv' := fkRectOneAddMulTwoSubOne_int_ediv_two k hk1
       simp only [hkdiv, hkdiv'] at *)
    | skip
  all_goals try (split_ifs at *)
  all_goals
    try simp only [fkRectNotEven_height_pred, fkRectNotEven_mul_two_sub_one,
      fkRectWidth_pred_int_cast,
      fkRectHeight_pred_int_cast, fkRectHeight_int_sub_one_ediv_two,
      fkRectHeight_int_sub_one_add_one_ediv_two,
      fkRectHeight_int_negOne_add_ediv_two,
      fkRectHeight_one_add_negOne_add_ediv_two,
      fkRectInt_add_self_ediv_two,
      fkRectInt_add_self_add_one_ediv_two,
      fkRectInt_add_self_add_two_ediv_two,
      fkRectMulTwoSubOne_int_ediv_two,
      fkRectOneAddMulTwoSubOne_int_ediv_two,
      fkRectFinPred_int_cast,
      fkRectAddSelfSubOne_int_cast,
      fkRectAddSelfSubOne_int_ediv_two,
      fkRectAddSelfSubOne_add_one_int_ediv_two]
  all_goals
    first
    | (have hxzero : x.val = 0 := by omega
       simp only [hxzero, Nat.zero_sub, Nat.cast_zero] at *)
    | (have hxpred := fkRectFinPred_int_cast x (by omega)
       rw [hxpred] at *)
    | skip
  all_goals
    first
    | (have hkzero : k = 0 := by omega
       simp only [hkzero, Nat.zero_mul, Nat.zero_add, Nat.sub_self,
         Nat.cast_zero] at *)
    | (have hkpredCast := fkRectAddSelfSubOne_int_cast k (by omega)
       have hkpredDiv := fkRectAddSelfSubOne_int_ediv_two k (by omega)
       have hkpredDiv' :=
         fkRectAddSelfSubOne_add_one_int_ediv_two k (by omega)
       simp only [hkpredCast, hkpredDiv, hkpredDiv'] at *)
    | skip
  all_goals norm_num at *
  all_goals ring_nf at *
  all_goals
    try simp only [fkRectWidth_pred_int_cast,
      fkRectHeight_pred_int_cast,
      fkRectHeight_int_negOne_add_ediv_two,
      fkRectHeight_one_add_negOne_add_ediv_two,
      fkRectInt_one_add_mul_two_ediv_two,
      fkRectInt_two_add_mul_two_ediv_two,
      fkRectInt_neg_one_add_mul_two_ediv_two] at *
  all_goals try (rw [fkRectWidth_pred_int_cast R] at *)
  all_goals try (rw [fkRectHeight_int_ediv_two R] at *)
  all_goals try (rw [fkRectHeight_int_negOne_add_ediv_two R] at *)
  all_goals try (rw [fkRectInt_one_add_mul_two_ediv_two] at *)
  all_goals try (rw [fkRectInt_two_add_mul_two_ediv_two] at *)
  all_goals try (rw [fkRectInt_neg_one_add_mul_two_ediv_two] at *)
  all_goals ring_nf at *
  all_goals try norm_num
  all_goals try (rw [fkRectHeight_int_sub_one_ediv_two R] at *)
  all_goals try (rw [fkRectHeight_int_negOne_add_ediv_two R] at *)
  all_goals try norm_num
  all_goals
    have hwidthGt := R.width_gt_two
    have hheightGt := R.height_gt_two
    have hwidthGtInt : (2 : Int) < R.width := by exact_mod_cast hwidthGt
    have hheightGtInt : (2 : Int) < R.height := by exact_mod_cast hheightGt
    try (rw [fkRectWidth_pred_int_cast R] at *)
    try (rw [fkRectHeight_int_ediv_two R] at *)
    try (rw [fkRectHeight_int_negTwo_add_ediv_two R] at *)
    try (rw [fkRectInt_three_add_mul_two_ediv_two] at *)
    try (rw [fkRectInt_neg_two_add_mul_two_ediv_two] at *)
  all_goals
    try simp_all only [fkRectNotEven_height_pred,
      fkRectNotEven_mul_two_sub_one]
  all_goals try constructor
  all_goals ring_nf at *
  all_goals
    first
    | exact (fkRectNotEven_mul_two_sub_one k (by omega)) (by assumption)
    | linarith
    | omega


end
end StatMech.FrontierD
