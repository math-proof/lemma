/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part4


namespace StatMech

namespace Exact3D

namespace StableBlockWithRemainder

theorem remainder_zero {n : ℕ} (S : StableBlockWithRemainder n) :
    S.remainder (0 : Fin n → ℝ) = 0 := by
  funext i
  have hle : |S.remainder (0 : Fin n → ℝ) i| ≤ 0 := by
    simpa [RatInterval.supNormVec] using
      S.remainder_bound (0 : Fin n → ℝ) i
  have habs : |S.remainder (0 : Fin n → ℝ) i| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp habs


theorem step_zero {n : ℕ} (S : StableBlockWithRemainder n) :
    S.step (0 : Fin n → ℝ) = 0 := by
  funext i
  have hrem := congrFun S.remainder_zero i
  simp [step, RatInterval.matVec, hrem]


theorem iterate_zero {n : ℕ} (S : StableBlockWithRemainder n) (k : ℕ) :
    S.iterate k (0 : Fin n → ℝ) = 0 := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, S.step_zero]


theorem apply_bound {n : ℕ} (S : StableBlockWithRemainder n)
    (x : Fin n → ℝ) (i : Fin n) :
    |S.step x i| ≤ S.coordinateConstant * RatInterval.supNormVec x := by
  have hlinear :
      |RatInterval.matVec S.linear x i| ≤
        (S.linear_contraction.c : ℝ) * RatInterval.supNormVec x :=
    S.linear_contraction.apply_bound S.enclosure_sound x i
  have hrem :
      |S.remainder x i| ≤
        (S.remainder_lipschitz.upper : ℝ) * RatInterval.supNormVec x :=
    S.remainder_bound x i
  calc
    |S.step x i| = |RatInterval.matVec S.linear x i + S.remainder x i| := rfl
    _ ≤ |RatInterval.matVec S.linear x i| + |S.remainder x i| := abs_add_le _ _
    _ ≤ (S.linear_contraction.c : ℝ) * RatInterval.supNormVec x +
        (S.remainder_lipschitz.upper : ℝ) * RatInterval.supNormVec x := by
      exact add_le_add hlinear hrem
    _ = ((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ) *
        RatInterval.supNormVec x := by
      norm_num [IntervalLipschitzConstant.upper]
      ring


theorem coordinateConstant_nonneg {n : ℕ} (S : StableBlockWithRemainder n) :
    0 ≤ S.coordinateConstant := by
  have hq :
      0 ≤ S.linear_contraction.c + S.remainder_lipschitz.upper :=
    add_nonneg S.linear_contraction.c_nonneg
      S.remainder_lipschitz.upper_nonneg
  have hqℝ :
      (0 : ℝ) ≤
        ((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [coordinateConstant] using hqℝ


theorem contraction_constant_lt_one {n : ℕ} (S : StableBlockWithRemainder n) :
    S.coordinateConstant < 1 := by
  have hqℝ :
      (((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ) <
        (1 : ℝ)) := by
    exact_mod_cast S.total_lt_one
  simpa [coordinateConstant] using hqℝ


theorem l1StepConstant_nonneg {n : ℕ} (S : StableBlockWithRemainder n) :
    0 ≤ S.l1StepConstant := by
  exact mul_nonneg (Nat.cast_nonneg n) S.coordinateConstant_nonneg


theorem ofLinearRowSum_l1StepConstant {n : ℕ}
    (linear : Fin n → Fin n → ℝ) {enclosure : RatInterval.IntervalMatrix n n}
    (enclosure_sound : RatInterval.MatrixMem linear enclosure)
    (linear_contraction : RatInterval.RowSumContraction enclosure) :
    (ofLinearRowSum linear enclosure_sound linear_contraction).l1StepConstant =
      (n : ℝ) * (linear_contraction.c : ℝ) := by
  simp [l1StepConstant, coordinateConstant, ofLinearRowSum,
    IntervalLipschitzConstant.zero, IntervalLipschitzConstant.upper,
    RatInterval.point]


theorem step_supNormVec_bound {n : ℕ} (S : StableBlockWithRemainder n)
    (x : Fin n → ℝ) :
    RatInterval.supNormVec (S.step x) ≤
      S.l1StepConstant * RatInterval.supNormVec x := by
  classical
  calc
    RatInterval.supNormVec (S.step x) =
        ∑ i : Fin n, |S.step x i| := rfl
    _ ≤ ∑ _i : Fin n, S.coordinateConstant * RatInterval.supNormVec x := by
      exact Finset.sum_le_sum fun i _ => S.apply_bound x i
    _ = S.l1StepConstant * RatInterval.supNormVec x := by
      simp [l1StepConstant, Finset.sum_const, nsmul_eq_mul]
      ring


theorem step_mem_l1_ball_of_l1StepConstant_le_one {n : ℕ}
    (S : StableBlockWithRemainder n) {r : ℝ}
    (hS : S.l1StepConstant ≤ 1) (hr : 0 ≤ r) {x : Fin n → ℝ}
    (hx : RatInterval.supNormVec x ≤ r) :
    RatInterval.supNormVec (S.step x) ≤ r := by
  calc
    RatInterval.supNormVec (S.step x) ≤
        S.l1StepConstant * RatInterval.supNormVec x :=
      S.step_supNormVec_bound x
    _ ≤ S.l1StepConstant * r := by
      exact mul_le_mul_of_nonneg_left hx S.l1StepConstant_nonneg
    _ ≤ 1 * r := by
      exact mul_le_mul_of_nonneg_right hS hr
    _ = r := by ring


theorem iterate_supNormVec_bound {n : ℕ} (S : StableBlockWithRemainder n)
    (k : ℕ) (x : Fin n → ℝ) :
    RatInterval.supNormVec (S.iterate k x) ≤
      S.l1StepConstant ^ k * RatInterval.supNormVec x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      calc
        RatInterval.supNormVec (S.iterate (k + 1) x) =
            RatInterval.supNormVec (S.step (S.iterate k x)) := rfl
        _ ≤ S.l1StepConstant * RatInterval.supNormVec (S.iterate k x) :=
          S.step_supNormVec_bound (S.iterate k x)
        _ ≤ S.l1StepConstant *
            (S.l1StepConstant ^ k * RatInterval.supNormVec x) := by
          exact mul_le_mul_of_nonneg_left ih S.l1StepConstant_nonneg
        _ = S.l1StepConstant ^ (k + 1) * RatInterval.supNormVec x := by
          rw [pow_succ']
          ring


theorem tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one {n : ℕ}
    (S : StableBlockWithRemainder n)
    (hS : S.l1StepConstant < 1) (x : Fin n → ℝ) :
    Filter.Tendsto (fun k : ℕ => RatInterval.supNormVec (S.iterate k x))
      Filter.atTop (nhds 0) := by
  have hpow :
      Filter.Tendsto (fun k : ℕ => S.l1StepConstant ^ k) Filter.atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one S.l1StepConstant_nonneg hS
  have hupper :
      Filter.Tendsto
        (fun k : ℕ =>
          S.l1StepConstant ^ k * RatInterval.supNormVec x)
        Filter.atTop (nhds 0) := by
    simpa using
      hpow.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => RatInterval.supNormVec x)
          Filter.atTop (nhds (RatInterval.supNormVec x)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds 0)) hupper ?_ ?_
  · intro k
    exact RatInterval.supNormVec_nonneg (S.iterate k x)
  · intro k
    exact S.iterate_supNormVec_bound k x


theorem iterate_mem_l1_ball_of_l1StepConstant_le_one {n : ℕ}
    (S : StableBlockWithRemainder n) {r : ℝ}
    (hS : S.l1StepConstant ≤ 1) (hr : 0 ≤ r) {x : Fin n → ℝ}
    (hx : RatInterval.supNormVec x ≤ r) (k : ℕ) :
    RatInterval.supNormVec (S.iterate k x) ≤ r := by
  induction k with
  | zero =>
      simpa [iterate] using hx
  | succ k ih =>
      exact S.step_mem_l1_ball_of_l1StepConstant_le_one hS hr ih


end StableBlockWithRemainder
end Exact3D
end StatMech
