/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve.Part3
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem mfp2_singleBit_q_gt_2_false : ¬ mfp_SingleBitQGt2 (9 / 10) := by
  intro H
  have h := H (1 / 2) (by norm_num) (by norm_num) 1 0
  rw [show |(1:ℝ)| = 1 by norm_num, show |(0:ℝ)| = 0 by norm_num] at h
  rw [show (2:ℝ) - 1 / 2 = 3 / 2 by norm_num] at h
  rw [Real.one_rpow] at h
  rw [Real.zero_rpow (by norm_num : (3:ℝ) / 2 ≠ 0)] at h
  rw [show (2:ℝ) / (3 / 2) = 4 / 3 by norm_num] at h
  rw [show ((1 - 9 / 10) * 1 + 9 / 10 * 0 : ℝ) = 1 / 10 by norm_num] at h
  have hLHS : ((1:ℝ) / 10) ^ 2 + (1 - 1 / 2) * (9 / 10 * (1 - 9 / 10)) * (1 - 0) ^ 2 = 11 / 200 := by
    norm_num
  rw [hLHS] at h
  
  have hcontra : ((1:ℝ) / 10) ^ ((4:ℝ) / 3) < 11 / 200 := by
    have hy : (0:ℝ) ≤ (11:ℝ) / 200 := by norm_num
    have hcube_x : (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) ^ (3:ℕ) = ((1:ℝ) / 10) ^ (4:ℝ) := by
      rw [← Real.rpow_natCast (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h10_4 : ((1:ℝ) / 10) ^ (4:ℝ) = 1 / 10000 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hlt : (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) ^ (3:ℕ) < ((11:ℝ) / 200) ^ (3:ℕ) := by
      rw [hcube_x, h10_4]; norm_num
    by_contra hc
    rw [not_lt] at hc
    exact absurd (pow_le_pow_left₀ hy hc 3) (not_le.mpr hlt)
  linarith


end StatMech.Probability
