/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part12


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptionalMirrorPointwiseProjection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    Function.Injective
      (survivalExceptionalMirrorPointwiseProjection R level walkLength
        start target hstart hlevel) := by
  intro a b hab
  apply survivalExceptionalMirrorProjection_injective R level walkLength
    start target hstart hlevel
  apply Prod.ext
  · simpa [survivalExceptionalMirrorPointwiseProjection,
        survivalExceptionalMirrorProjection] using
      congrArg (fun z => z.1) hab
  · apply Subtype.ext
    simpa [survivalExceptionalMirrorPointwiseProjection,
        survivalExceptionalMirrorProjection] using
      congrArg (fun z => z.2.1) hab


theorem survivalExceptionalMirrorFamily_weight_le_inv_leftGap
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      1 / (level : Real) := by
  let p := leftGapNeighbor level hlevel
  let q := leftGapLeft level
  have hcountNat :
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) ≤
        Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          2 ^ walkLength := by
    calc
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) ≤
          Nat.card (IsingLineChoicePathFamily level walkLength p q ×
            {v : List Bool // v.length = walkLength}) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalMirrorProjection R level walkLength start target
            hstart hlevel)
          (survivalExceptionalMirrorProjection_injective R level walkLength
            start target hstart hlevel)
      _ = Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          Nat.card {v : List Bool // v.length = walkLength} := by
        rw [Nat.card_prod]
      _ = _ := by rw [natCard_boolListLength]
  have hcountReal :
      (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength := by
    exact_mod_cast hcountNat
  have hline :
      (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength ≤ 1 / (level : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [leftGapNeighbor, leftGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor level walkLength hlevel)
  calc
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
        ((Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / (level : Real) := hline


theorem survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap
    (R level walkLength : Nat) (start : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    (Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int)
        walkLength) : Real) / 4 ^ walkLength ≤
      1 / (level : Real) := by
  let p := leftGapNeighbor level hlevel
  let q := leftGapLeft level
  have hcountNat :
      Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int)
        walkLength) ≤
        Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          2 ^ walkLength := by
    calc
      _ ≤ Nat.card (IsingLineChoicePathFamily level walkLength p q ×
          {v : List Bool // v.length = walkLength}) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalMirrorProjectionAll R level walkLength start
            hstart hlevel)
          (survivalExceptionalMirrorProjectionAll_injective R level walkLength
            start hstart hlevel)
      _ = Nat.card (IsingLineChoicePathFamily level walkLength p q) *
          Nat.card {v : List Bool // v.length = walkLength} := by
        rw [Nat.card_prod]
      _ = _ := by rw [natCard_boolListLength]
  have hcountReal :
      (Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int)
          walkLength) : Real) ≤
        (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength := by
    exact_mod_cast hcountNat
  have hline :
      (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength ≤ 1 / (level : Real) := by
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [leftGapNeighbor, leftGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor level walkLength hlevel)
  calc
    _ ≤ ((Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) *
          (2 : Real) ^ walkLength) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (Nat.card (IsingLineChoicePathFamily level walkLength p q) : Real) /
          (2 : Real) ^ walkLength := by
      rw [show (4 : Real) ^ walkLength =
          (2 : Real) ^ walkLength * (2 : Real) ^ walkLength by
        rw [← mul_pow]
        norm_num]
      field_simp
    _ ≤ 1 / (level : Real) := hline


theorem survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) : Real) / 4 ^ walkLength ≤
      (1 / (level : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
  let p := leftGapNeighbor level hlevel
  let q := leftGapLeft level
  let H := IsingLineChoicePathFamily level walkLength p q
  let V := VerticalChoicePathFamily walkLength start.2 target.2
  have hcountNat :
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
        walkLength target) ≤ Nat.card H * Nat.card V := by
    calc
      Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) ≤ Nat.card (H × V) :=
        Nat.card_le_card_of_injective
          (survivalExceptionalMirrorPointwiseProjection R level walkLength
            start target hstart hlevel)
          (survivalExceptionalMirrorPointwiseProjection_injective R level
            walkLength start target hstart hlevel)
      _ = _ := by rw [Nat.card_prod]
  have hcountReal :
      (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) ≤
        (Nat.card H : Real) * (Nat.card V : Real) := by
    exact_mod_cast hcountNat
  have hline : (Nat.card H : Real) / (2 : Real) ^ walkLength ≤
      1 / (level : Real) := by
    dsimp [H]
    rw [← isingLineStoppedKernel_eq_natCard_choicePath_div]
    dsimp [p, q]
    simpa [leftGapNeighbor, leftGapLeft] using
      (isingLineStoppedKernel_left_of_rightNeighbor level walkLength hlevel)
  have hvertical : (Nat.card V : Real) / (2 : Real) ^ walkLength =
      isingLineBinomialKernel walkLength start.2 target.2 := by
    dsimp [V]
    symm
    exact isingLineBinomialKernel_eq_natCard_verticalChoicePath_div
      walkLength start.2 target.2
  calc
    (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
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
    _ ≤ (1 / (level : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 :=
      mul_le_mul_of_nonneg_right hline
        (isingLineBinomialKernel_nonneg walkLength start.2 target.2)


theorem survivingFirstHitFamily_weight_dist_le_inv_gaps
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start (level : Int)
          walkLength target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint (level : Int) start) (level : Int)
          walkLength target)) : Real) / 4 ^ walkLength ≤
      1 / ((R - level : Nat) : Real) + 1 / (level : Real) := by
  have hdistNat := natDist_survivingFirstHitFamily_le_exceptions R start
    (level : Int) walkLength target
  have hdistReal :
      (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R start (level : Int)
            walkLength target))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint (level : Int) start) (level : Int)
            walkLength target)) : Real) ≤
        (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) := by
    exact_mod_cast hdistNat
  calc
    _ ≤ ((Nat.card (SurvivalExceptionalFirstHitFamily R start
          (level : Int) walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hdistReal (by positivity)
    _ = (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength := by ring
    _ ≤ 1 / ((R - level : Nat) : Real) + 1 / (level : Real) :=
      add_le_add
        (survivalExceptionalFirstHitFamily_weight_le_inv_rightGap R level
          walkLength start target hstart hlevel hgap)
        (survivalExceptionalMirrorFamily_weight_le_inv_leftGap R level
          walkLength start target hstart hlevel)


theorem survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    (Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start (level : Int)
          walkLength target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint (level : Int) start) (level : Int)
          walkLength target)) : Real) / 4 ^ walkLength ≤
      (1 / ((R - level : Nat) : Real) + 1 / (level : Real)) *
        isingLineBinomialKernel walkLength start.2 target.2 := by
  have hdistNat := natDist_survivingFirstHitFamily_le_exceptions R start
    (level : Int) walkLength target
  have hdistReal :
      (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R start (level : Int)
            walkLength target))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint (level : Int) start) (level : Int)
            walkLength target)) : Real) ≤
        (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) := by
    exact_mod_cast hdistNat
  calc
    _ ≤ ((Nat.card (SurvivalExceptionalFirstHitFamily R start
          (level : Int) walkLength target) : Real) +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real)) / 4 ^ walkLength :=
      div_le_div_of_nonneg_right hdistReal (by positivity)
    _ = (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength +
        (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int)
          walkLength target) : Real) / 4 ^ walkLength := by ring
    _ ≤ (1 / ((R - level : Nat) : Real)) *
          isingLineBinomialKernel walkLength start.2 target.2 +
        (1 / (level : Real)) *
          isingLineBinomialKernel walkLength start.2 target.2 :=
      add_le_add
        (survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial
          R level walkLength start target hstart hlevel hgap)
        (survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial
          R level walkLength start target hstart hlevel)
    _ = _ := by ring


theorem survivingFirstHitFamily_diffusive_weight_dist_le
    (R level ρ : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hρ : 0 < ρ)
    (hleft : ρ + 1 ≤ level) (hright : level + 1 + ρ ≤ R) :
    (Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start (level : Int)
          (ρ * ρ) target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint (level : Int) start) (level : Int)
          (ρ * ρ) target)) : Real) / 4 ^ (ρ * ρ) ≤
      4 / (ρ : Real) ^ 2 := by
  have hbase :=
    survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial R level
      (ρ * ρ) start target hstart (by omega) (by omega)
  let K := isingLineBinomialKernel (ρ * ρ) start.2 target.2
  have hK0 : 0 ≤ K := isingLineBinomialKernel_nonneg _ _ _
  have hKsq := isingLineBinomialKernel_sq_le (ρ * ρ) start.2 target.2
  norm_num [Nat.cast_add, Nat.cast_mul] at hKsq
  have hden : 0 < (ρ : Real) ^ 2 + 1 := by positivity
  have hKsq' : K ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2 := by
    apply (le_div_iff₀ hden).mp
    dsimp [K]
    convert hKsq using 1 <;> ring
  have hρReal : 0 < (ρ : Real) := by positivity
  have hK : K ≤ 2 / (ρ : Real) := by
    apply (le_div_iff₀ hρReal).2
    have hprod0 : 0 ≤ (ρ : Real) * K := mul_nonneg hρReal.le hK0
    have hprodSq : ((ρ : Real) * K) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg K]
    nlinarith
  have hrightGap : (ρ : Real) ≤ (R - level : Nat) := by
    exact_mod_cast (show ρ ≤ R - level by omega)
  have hleftGap : (ρ : Real) ≤ level := by
    exact_mod_cast (show ρ ≤ level by omega)
  have hinvRight : 1 / ((R - level : Nat) : Real) ≤
      1 / (ρ : Real) := one_div_le_one_div_of_le hρReal hrightGap
  have hinvLeft : 1 / (level : Real) ≤ 1 / (ρ : Real) :=
    one_div_le_one_div_of_le hρReal hleftGap
  have hgap : 1 / ((R - level : Nat) : Real) + 1 / (level : Real) ≤
      2 / (ρ : Real) := by
    calc
      _ ≤ 1 / (ρ : Real) + 1 / (ρ : Real) :=
        add_le_add hinvRight hinvLeft
      _ = _ := by ring
  calc
    _ ≤ (1 / ((R - level : Nat) : Real) + 1 / (level : Real)) * K :=
      hbase
    _ ≤ (2 / (ρ : Real)) * K :=
      mul_le_mul_of_nonneg_right hgap hK0
    _ ≤ (2 / (ρ : Real)) * (2 / (ρ : Real)) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    _ = 4 / (ρ : Real) ^ 2 := by ring

end IsingDiagonalWalkHitSplit
end StatMech.Universality
