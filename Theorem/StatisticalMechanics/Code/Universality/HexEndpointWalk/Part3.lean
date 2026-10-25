/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3


namespace StatMech.Universality

open HexWalk

@[simp]
theorem hexEndpointSAWCountR_zero (a : ℂ) (h0 : ℤ) :
    hexEndpointSAWCountR a h0 0 = 1 := by
  simp [hexEndpointSAWCountR, hexEndpointSAWCount_zero]

@[simp]
theorem hexEndpointSAWCountR_succ (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hexEndpointSAWCountR a h0 (n + 1) = 2 * hlc_sawCountR a h0 n := by
  simp [hexEndpointSAWCountR, hexEndpointSAWCount_succ, hlc_sawCountR]

@[simp]
theorem hexEndpointCoeffWeight_zero (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexEndpointCoeffWeight a h0 x 0 = 1 := by
  simp [hexEndpointCoeffWeight]


theorem hexEndpointCoeffWeight_succ (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) :
    hexEndpointCoeffWeight a h0 x (n + 1) =
      (2 * x) * (hlc_sawCountR a h0 n * x ^ n) := by
  rw [hexEndpointCoeffWeight, hexEndpointSAWCountR_succ, pow_succ]
  ring


theorem hexEndpoint_summable_iff_hlc (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hx : x ≠ 0) :
    Summable (hexEndpointCoeffWeight a h0 x) ↔
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
  calc
    Summable (hexEndpointCoeffWeight a h0 x) ↔
        Summable (fun n => hexEndpointCoeffWeight a h0 x (n + 1)) :=
      (summable_nat_add_iff 1).symm
    _ ↔ Summable
        (fun n => (2 * x) * (hlc_sawCountR a h0 n * x ^ n)) :=
      summable_congr (hexEndpointCoeffWeight_succ a h0 x)
    _ ↔ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
      summable_mul_left_iff (mul_ne_zero (by norm_num) hx)


theorem hexEndpoint_summable_iff_hlc_of_pos (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hx : 0 < x) :
    Summable (hexEndpointCoeffWeight a h0 x) ↔
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  hexEndpoint_summable_iff_hlc a h0 hx.ne'


theorem hexEndpoint_not_summable_iff_hlc (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hx : 0 < x) :
    (¬ Summable (hexEndpointCoeffWeight a h0 x)) ↔
      ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  not_congr (hexEndpoint_summable_iff_hlc_of_pos a h0 hx)


theorem hexEndpoint_tsum_eq_of_summable (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hcoeff : Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n)) :
    (∑' n, hexEndpointCoeffWeight a h0 x n) =
      1 + 2 * x * ∑' n, hlc_sawCountR a h0 n * x ^ n := by
  by_cases hx : x = 0
  · subst x
    have hend : Summable (hexEndpointCoeffWeight a h0 0) := by
      apply (hasSum_single 0 (fun n hn => ?_)).summable
      cases n with
      | zero => contradiction
      | succ n => simp [hexEndpointCoeffWeight]
    have hsplit := hend.sum_add_tsum_nat_add 1
    calc
      (∑' n, hexEndpointCoeffWeight a h0 0 n) =
          hexEndpointCoeffWeight a h0 0 0 +
            ∑' n, hexEndpointCoeffWeight a h0 0 (n + 1) := by
        simpa using hsplit.symm
      _ = 1 := by simp [hexEndpointCoeffWeight]
      _ = 1 + 2 * 0 * ∑' n, hlc_sawCountR a h0 n * 0 ^ n := by ring
  · have hend : Summable (hexEndpointCoeffWeight a h0 x) :=
      (hexEndpoint_summable_iff_hlc a h0 hx).2 hcoeff
    have hsplit := hend.sum_add_tsum_nat_add 1
    calc
      (∑' n, hexEndpointCoeffWeight a h0 x n) =
          1 + ∑' n, hexEndpointCoeffWeight a h0 x (n + 1) := by
        simpa using hsplit.symm
      _ = 1 + ∑' n, (2 * x) * (hlc_sawCountR a h0 n * x ^ n) := by
        congr 1
        apply tsum_congr
        exact hexEndpointCoeffWeight_succ a h0 x
      _ = 1 + 2 * x * ∑' n, hlc_sawCountR a h0 n * x ^ n := by
        rw [tsum_mul_left]


theorem hexEndpoint_hasSum_of_hlc_hasSum (a : ℂ) (h0 : ℤ) {x z : ℝ}
    (hcoeff : HasSum (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) z) :
    HasSum (hexEndpointCoeffWeight a h0 x) (1 + 2 * x * z) := by
  have hsum := hexEndpoint_tsum_eq_of_summable a h0 hcoeff.summable
  have hend : Summable (hexEndpointCoeffWeight a h0 x) := by
    by_cases hx : x = 0
    · subst x
      apply (hasSum_single 0 (fun n hn => ?_)).summable
      cases n with
      | zero => contradiction
      | succ n => simp [hexEndpointCoeffWeight]
    · exact (hexEndpoint_summable_iff_hlc a h0 hx).2 hcoeff.summable
  rw [← hcoeff.tsum_eq, ← hsum]
  exact hend.hasSum

end StatMech.Universality
