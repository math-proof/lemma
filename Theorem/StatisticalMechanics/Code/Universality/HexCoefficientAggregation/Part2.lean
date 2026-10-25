/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


theorem hlc_coeffWeight_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ hlc_coeffWeight a h0 x n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)


@[simp] theorem hlc_coeffWeight_zero (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hlc_coeffWeight a h0 x 0 = 1 := by
  simp [hlc_coeffWeight, hlc_sawCount_zero]


@[simp] theorem hlc_coeffWeight_zero_fugacity (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hlc_coeffWeight a h0 0 n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simp [hlc_coeffWeight]


theorem hzc_coeffWeight_succ_eq_mul_hlc (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) :
    hzc_coeffWeight a h0 x (n + 1) = x * hlc_coeffWeight a h0 x n := by
  unfold hzc_coeffWeight hlc_coeffWeight hlc_sawCount
  rw [pow_succ]
  ring


theorem hzc_coeff_sum_shift (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), hzc_coeffWeight a h0 x k =
      x * ∑ n ∈ Finset.range N, hlc_coeffWeight a h0 x n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ (f := hzc_coeffWeight a h0 x) (n := N + 1), ih,
        Finset.sum_range_succ (f := hlc_coeffWeight a h0 x) (n := N), mul_add,
        hzc_coeffWeight_succ_eq_mul_hlc]


theorem hlc_trunc_sum_eq_mul_coeff_sum (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ ts ∈ hzc_truncFinset a h0 (N + 1), hexSAWwt a h0 x ts =
      x * ∑ n ∈ Finset.range N, hlc_coeffWeight a h0 x n := by
  rw [hzc_trunc_sum_eq_coeff_sum, hzc_coeff_sum_shift]


theorem hzc_coeff_summable_iff_hlc_coeff_summable
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (hzc_coeffWeight a h0 x) ↔ Summable (hlc_coeffWeight a h0 x) := by
  rcases hx.eq_or_lt with rfl | hx
  · constructor
    · intro _
      exact (hasSum_single 0 (fun n hn => by simp [hn])).summable
    · intro _
      exact (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).congr
        (fun n => (hzc_coeffWeight_zero_fugacity a h0 n).symm)
  · calc
      Summable (hzc_coeffWeight a h0 x) ↔
          Summable (fun n => hzc_coeffWeight a h0 x (n + 1)) :=
        (summable_nat_add_iff 1).symm
      _ ↔ Summable (fun n => x * hlc_coeffWeight a h0 x n) :=
        summable_congr (hzc_coeffWeight_succ_eq_mul_hlc a h0 x)
      _ ↔ Summable (hlc_coeffWeight a h0 x) := summable_mul_left_iff hx.ne'


theorem hlc_summable_iff (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) ↔
      Summable (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n) := by
  exact (hzc_walk_summable_iff_coeff_summable a h0 hx).trans
    ((hzc_coeff_summable_iff_hlc_coeff_summable a h0 hx).trans
      (by rfl : Summable (hlc_coeffWeight a h0 x) ↔
        Summable (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n)))


theorem hzc_coeff_tsum_eq_mul_hlc_coeff_tsum
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' n, hzc_coeffWeight a h0 x n) = x * ∑' n, hlc_coeffWeight a h0 x n := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · by_cases hvertex : Summable (hzc_coeffWeight a h0 x)
    · have htail := hvertex.sum_add_tsum_nat_add 1
      calc
        (∑' n, hzc_coeffWeight a h0 x n) =
            ∑' n, hzc_coeffWeight a h0 x (n + 1) := by
              simpa using htail.symm
        _ = ∑' n, x * hlc_coeffWeight a h0 x n := by
          apply tsum_congr
          exact hzc_coeffWeight_succ_eq_mul_hlc a h0 x
        _ = x * ∑' n, hlc_coeffWeight a h0 x n := tsum_mul_left
    · have hstep : ¬ Summable (hlc_coeffWeight a h0 x) := by
        rwa [hzc_coeff_summable_iff_hlc_coeff_summable a h0 hx.le] at hvertex
      rw [tsum_eq_zero_of_not_summable hvertex, tsum_eq_zero_of_not_summable hstep, mul_zero]


theorem hlc_tsum_eq (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' ts : List ℤ, hexSAWwt a h0 x ts) =
      x * ∑' n : ℕ, (hlc_sawCount a h0 n : ℝ) * x ^ n := by
  rw [hzc_tsum_eq_coeff_tsum a h0 hx,
    hzc_coeff_tsum_eq_mul_hlc_coeff_tsum a h0 hx]
  rfl


theorem hlc_walk_hasSum_of_coeff_hasSum (a : ℂ) (h0 : ℤ) {x z : ℝ} (hx : 0 ≤ x)
    (hcoeff : HasSum (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n) z) :
    HasSum (fun ts : List ℤ => hexSAWwt a h0 x ts) (x * z) := by
  have hwalk : Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) :=
    (hlc_summable_iff a h0 hx).mpr hcoeff.summable
  rw [← hcoeff.tsum_eq, ← hlc_tsum_eq a h0 hx]
  exact hwalk.hasSum

end StatMech.Universality
