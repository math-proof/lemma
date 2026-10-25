/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part4


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem natCard_boolListLength (t : Nat) :
    Nat.card {v : List Bool // v.length = t} = 2 ^ t := by
  change Nat.card (List.Vector Bool t) = 2 ^ t
  rw [Nat.card_congr (Equiv.vectorEquivFin Bool t)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  simp


theorem natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
      Nat.card (IsingLineChoicePathFamily (R - level) walkLength
        (rightGapNeighbor R level hgap) (rightGapLeft R level)) *
          2 ^ walkLength := by
  calc
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
        Nat.card (IsingLineChoicePathFamily (R - level) walkLength
            (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
          {v : List Bool // v.length = walkLength}) :=
      Nat.card_le_card_of_injective
        (survivalExceptionalProjection R level walkLength start target
          hstart hlevel hgap)
        (survivalExceptionalFirstHitFamily_projection_injective R level
          walkLength start target hstart hlevel hgap)
    _ = Nat.card (IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level)) *
        Nat.card {v : List Bool // v.length = walkLength} := by
      rw [Nat.card_prod]
    _ = _ := by rw [natCard_boolListLength]


theorem survivalExceptionalFirstHitFamily_weight_le_inv_rightGap
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      1 / ((R - level : Nat) : Real) := by
  let p := rightGapNeighbor R level hgap
  let q := rightGapLeft R level
  have hcountNat :=
    natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow R level
      walkLength start target hstart hlevel hgap
  have hcountReal :
      (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength := by
    dsimp [p, q]
    exact_mod_cast hcountNat
  have hgapPos : 0 < R - level := by omega
  have hline :
      (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength ≤
        1 / ((R - level : Nat) : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [rightGapNeighbor, rightGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor
        (R - level) walkLength hgapPos)
  calc
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / ((R - level : Nat) : Real) := hline


theorem survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int)
        walkLength) : Real) / 4 ^ walkLength ≤
      1 / ((R - level : Nat) : Real) := by
  let p := rightGapNeighbor R level hgap
  let q := rightGapLeft R level
  have hcountNat :
      Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int)
        walkLength) ≤
        Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) *
          2 ^ walkLength := by
    calc
      _ ≤ Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q ×
          {v : List Bool // v.length = walkLength}) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalProjectionAll R level walkLength start
            hstart hlevel hgap)
          (survivalExceptionalProjectionAll_injective R level walkLength start
            hstart hlevel hgap)
      _ = Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) *
          Nat.card {v : List Bool // v.length = walkLength} := by
        rw [Nat.card_prod]
      _ = _ := by rw [natCard_boolListLength]
  have hcountReal :
      (Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int)
          walkLength) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength := by
    exact_mod_cast hcountNat
  have hline :
      (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength ≤
        1 / ((R - level : Nat) : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [rightGapNeighbor, rightGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor (R - level) walkLength
        (show 0 < R - level by omega))
  calc
    _ ≤ ((Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) * (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily (R - level) walkLength p q) :
          Real) / (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / ((R - level : Nat) : Real) := hline


theorem survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      (1 / ((R - level : Nat) : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
  let p := rightGapNeighbor R level hgap
  let q := rightGapLeft R level
  let H := IsingLineChoicePathFamily (R - level) walkLength p q
  let V := VerticalChoicePathFamily walkLength start.2 target.2
  have hcountNat :=
    natCard_survivalExceptionalFirstHitFamily_le_line_mul_vertical R level
      walkLength start target hstart hlevel hgap
  have hcountReal :
      (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card H : Real) * (Nat.card V : Real) := by
    dsimp [H, V, p, q]
    exact_mod_cast hcountNat
  have hgapPos : 0 < R - level := by omega
  have hline : (Nat.card H : Real) / (2 : Real) ^ walkLength ≤
      1 / ((R - level : Nat) : Real) := by
    dsimp [H]
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [rightGapNeighbor, rightGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor
        (R - level) walkLength hgapPos)
  have hvertical : (Nat.card V : Real) / (2 : Real) ^ walkLength =
      isingLineBinomialKernel walkLength start.2 target.2 := by
    dsimp [V]
    symm
    exact isingLineBinomialKernel_eq_natCard_verticalChoicePath_div
      walkLength start.2 target.2
  calc
    (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card H : Real) * (Nat.card V : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = ((Nat.card H : Real) / (2 : Real) ^ walkLength) *
        ((Nat.card V : Real) / (2 : Real) ^ walkLength) := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ = ((Nat.card H : Real) / (2 : Real) ^ walkLength) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
      rw [hvertical]
    _ ≤ (1 / ((R - level : Nat) : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 :=
      mul_le_mul_of_nonneg_right hline
        (isingLineBinomialKernel_nonneg walkLength start.2 target.2)

end IsingDiagonalWalkHitSplit
end StatMech.Universality
