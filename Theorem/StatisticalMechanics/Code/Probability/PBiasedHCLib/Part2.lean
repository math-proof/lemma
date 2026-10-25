/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Def.StatisticalMechanics.Code.Probability.PBiasedHCLib
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

theorem hclib_bracket {q t : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) (ht : |t| ≤ 1) :
    ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2
      ≤ (1 + (q - 1) * t ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2) := by
  set w := 1 + (q - 1) * t ^ 2 with hw
  have hq1 : 0 ≤ q - 1 := by linarith
  have hwpos : 0 < w := by rw [hw]; nlinarith [mul_nonneg hq1 (sq_nonneg t)]
  have hJ := hclib_jensen_two_point (r := q - 2) (by linarith) (by linarith) ht
  have hbase : (1 : ℝ) + t ^ 2 ≤ w := by rw [hw]; nlinarith [sq_nonneg t]
  have hmono : (1 + t ^ 2) ^ ((q - 2) / 2) ≤ w ^ ((q - 2) / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hI : ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2 ≤ w ^ ((q - 2) / 2) := le_trans hJ hmono
  have hsplit : w ^ ((q - 2) / 2) = w ^ ((q - 4) / 2) * w := by
    rw [show (q - 2) / 2 = (q - 4) / 2 + 1 by ring, Real.rpow_add hwpos, Real.rpow_one]
  have hwle : w ≤ 1 + (q - 1) ^ 2 * t ^ 2 := by
    rw [hw]; nlinarith [mul_nonneg (mul_nonneg hq1 hq1) (sq_nonneg t), sq_nonneg t,
      mul_nonneg hq1 (sq_nonneg t)]
  have hII : w ^ ((q - 2) / 2) ≤ w ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_left hwle (Real.rpow_nonneg hwpos.le _)
  linarith


theorem hclib_BracketResidue_of_le_four {q : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) :
    hclib_BracketResidue q :=
  fun _ ht => hclib_bracket hq2 hq4 ht


end StatMech.Probability
