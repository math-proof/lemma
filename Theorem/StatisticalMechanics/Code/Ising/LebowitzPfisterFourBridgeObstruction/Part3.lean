/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction.Part3


namespace StatMech.Ising

noncomputable section

theorem fourBridgeRankMass_sum (a b c d : Real) :
    fourBridgeRankMass a b c d 0 + fourBridgeRankMass a b c d 1 +
      fourBridgeRankMass a b c d 2 + fourBridgeRankMass a b c d 3 +
      fourBridgeRankMass a b c d 4 = 1 := by
  simp [fourBridgeRankMass]
  ring


theorem fourBridge_endpointSix_eq_rankCross (a b c d : Real) :
    a * b + 3 * a * d - a - b * c + c * d - 3 * c =
      64 * (fourBridgeRankMass a b c d 0 *
          fourBridgeRankMass a b c d 3 -
        fourBridgeRankMass a b c d 1 *
          fourBridgeRankMass a b c d 4) := by
  simp [fourBridgeRankMass]
  ring


theorem fourBridge_endpointFive_eq_rankCross (a b c d : Real) :
    2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c =
      32 * (fourBridgeRankMass a b c d 2 *
          (fourBridgeRankMass a b c d 0 -
            fourBridgeRankMass a b c d 4) +
        3 * (fourBridgeRankMass a b c d 0 *
            fourBridgeRankMass a b c d 3 -
          fourBridgeRankMass a b c d 1 *
            fourBridgeRankMass a b c d 4)) := by
  simp [fourBridgeRankMass]
  ring


theorem fourBridge_endpointFactors_nonpos_of_rank
    {a b c d : Real}
    (h2 : 0 <= fourBridgeRankMass a b c d 2)
    (h04 : fourBridgeRankMass a b c d 0 <=
      fourBridgeRankMass a b c d 4)
    (hcross : fourBridgeRankMass a b c d 0 *
        fourBridgeRankMass a b c d 3 <=
      fourBridgeRankMass a b c d 1 *
        fourBridgeRankMass a b c d 4) :
    2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c <= 0 ∧
      a * b + 3 * a * d - a - b * c + c * d - 3 * c <= 0 := by
  rw [fourBridge_endpointFive_eq_rankCross,
    fourBridge_endpointSix_eq_rankCross]
  constructor
  · have hbias : fourBridgeRankMass a b c d 2 *
        (fourBridgeRankMass a b c d 0 -
          fourBridgeRankMass a b c d 4) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos h2 (sub_nonpos.mpr h04)
    have hratio : fourBridgeRankMass a b c d 0 *
          fourBridgeRankMass a b c d 3 -
        fourBridgeRankMass a b c d 1 *
          fourBridgeRankMass a b c d 4 <= 0 := sub_nonpos.mpr hcross
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (sub_nonpos.mpr hcross)


theorem fourBridgeVarianceSkewPolynomial_eq_bernstein
    (t a b c d : Real) :
    fourBridgeVarianceSkewPolynomial t a b c d =
      fourBridgeVarianceSkewBernsteinCoeff a b c d 0 * (1 - t ^ 2) ^ 6 +
      6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 1 * t ^ 2 *
        (1 - t ^ 2) ^ 5 +
      15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 2 * (t ^ 2) ^ 2 *
        (1 - t ^ 2) ^ 4 +
      20 * fourBridgeVarianceSkewBernsteinCoeff a b c d 3 * (t ^ 2) ^ 3 *
        (1 - t ^ 2) ^ 3 +
      15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 4 * (t ^ 2) ^ 4 *
        (1 - t ^ 2) ^ 2 +
      6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 5 * (t ^ 2) ^ 5 *
        (1 - t ^ 2) +
      fourBridgeVarianceSkewBernsteinCoeff a b c d 6 * (t ^ 2) ^ 6 := by
  unfold fourBridgeVarianceSkewPolynomial
    fourBridgeVarianceSkewBernsteinCoeff
  ring


theorem fourBridgeVarianceSkewPolynomial_nonpos_of_bernstein
    {t a b c d : Real} (ht0 : 0 <= t) (ht1 : t <= 1)
    (hcoeff : forall i,
      fourBridgeVarianceSkewBernsteinCoeff a b c d i <= 0) :
    fourBridgeVarianceSkewPolynomial t a b c d <= 0 := by
  rw [fourBridgeVarianceSkewPolynomial_eq_bernstein]
  have hs0 : 0 <= t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 <= 1 := by nlinarith
  have hq0 : 0 <= 1 - t ^ 2 := sub_nonneg.mpr hs1
  have h0 := hcoeff (0 : Fin 7)
  have h1 := hcoeff (1 : Fin 7)
  have h2 := hcoeff (2 : Fin 7)
  have h3 := hcoeff (3 : Fin 7)
  have h4 := hcoeff (4 : Fin 7)
  have h5 := hcoeff (5 : Fin 7)
  have h6 := hcoeff (6 : Fin 7)
  have hterm0 : fourBridgeVarianceSkewBernsteinCoeff a b c d 0 *
      (1 - t ^ 2) ^ 6 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg h0 (pow_nonneg hq0 6)
  have hterm1 : 6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 1 *
      t ^ 2 * (1 - t ^ 2) ^ 5 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h1) hs0)
      (pow_nonneg hq0 5)
  have hterm2 : 15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 2 *
      (t ^ 2) ^ 2 * (1 - t ^ 2) ^ 4 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h2)
        (pow_nonneg hs0 2)) (pow_nonneg hq0 4)
  have hterm3 : 20 * fourBridgeVarianceSkewBernsteinCoeff a b c d 3 *
      (t ^ 2) ^ 3 * (1 - t ^ 2) ^ 3 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h3)
        (pow_nonneg hs0 3)) (pow_nonneg hq0 3)
  have hterm4 : 15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 4 *
      (t ^ 2) ^ 4 * (1 - t ^ 2) ^ 2 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h4)
        (pow_nonneg hs0 4)) (pow_nonneg hq0 2)
  have hterm5 : 6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 5 *
      (t ^ 2) ^ 5 * (1 - t ^ 2) <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h5)
        (pow_nonneg hs0 5)) hq0
  have hterm6 : fourBridgeVarianceSkewBernsteinCoeff a b c d 6 *
      (t ^ 2) ^ 6 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg h6 (pow_nonneg hs0 6)
  linarith


theorem fourBridgeTiltVariance_le_neg_iff
    {t a b c d : Real} (ht0 : 0 < t) (ht1 : t < 1)
    (hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 ≠ 0)
    (hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4 ≠ 0) :
    fourBridgeTiltVariance t a b c d <=
        fourBridgeTiltVariance (-t) a b c d <->
      fourBridgeVarianceSkewPolynomial t a b c d <= 0 := by
  let Pp := 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4
  let Pm := 1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4
  let F := fourBridgeVarianceSkewPolynomial t a b c d
  let C := 4 * t * (t - 1) * (t + 1)
  have hPp0 : Pp ≠ 0 := by simpa [Pp] using hPp
  have hPm0 : Pm ≠ 0 := by simpa [Pm] using hPm
  have hden : 0 < Pm ^ 2 * Pp ^ 2 :=
    mul_pos (sq_pos_of_ne_zero hPm0) (sq_pos_of_ne_zero hPp0)
  have hC : C < 0 := by
    dsimp [C]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht0) (sub_neg.mpr ht1))
      (by linarith)
  have hdiff :
      fourBridgeTiltVariance (-t) a b c d -
          fourBridgeTiltVariance t a b c d =
        C * F / (Pm ^ 2 * Pp ^ 2) := by
    unfold fourBridgeTiltVariance
    simp only [neg_sq, neg_mul, mul_neg]
    rw [show 1 + -(a * t) + b * t ^ 2 + c * (-t) ^ 3 +
        d * (-t) ^ 4 = Pm by dsimp [Pm]; ring]
    rw [show 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 = Pp by rfl]
    field_simp [hPp0, hPm0]
    dsimp [C, F, fourBridgeVarianceSkewPolynomial]
    ring
  constructor
  · intro hvar
    have hnonneg : 0 <= C * F / (Pm ^ 2 * Pp ^ 2) := by
      rw [<- hdiff]
      exact sub_nonneg.mpr hvar
    have hnum : 0 <= C * F := by
      have hm := mul_nonneg hnonneg hden.le
      rw [div_mul_cancel₀ _ hden.ne'] at hm
      exact hm
    by_contra hF
    have hFpos : 0 < F := lt_of_not_ge hF
    exact (not_lt_of_ge hnum) (mul_neg_of_neg_of_pos hC hFpos)
  · intro hF
    apply sub_nonneg.mp
    rw [hdiff]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hC.le hF) hden.le

end
end StatMech.Ising
