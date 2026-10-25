/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VarGapProve2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
import Def.StatisticalMechanics.Code.Probability.MasterFamilyProve
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem mfp_singleBit_q_gt_2_value : mfp_SingleBitQGt2 (1 / 2) := by
  intro u hu0 hu1 u₀ v₀
  set q : ℝ := 2 - u with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  have hq2 : q ≤ 2 := by rw [hq]; linarith
  
  have hval := pbt_two_point_value_of_core (p := 1 / 2) (q := q)
    (by norm_num) (by norm_num) hq1 hq2 (pbt_core_half hq1 hq2)
    (by rw [show (1:ℝ) - 1/2 = 1/2 by norm_num]; exact pbt_core_half hq1 hq2) u₀ v₀
  
  have hcoeff : (q - 1) * 4 * (1 / 2 : ℝ) ^ 2 * (1 - 1 / 2) ^ 2
      = (1 - u) * ((1 / 2 : ℝ) * (1 - 1 / 2)) := by rw [hq]; ring
  rw [hcoeff] at hval
  exact hval


theorem mfp_singleBit_route_dead {p : ℝ} (H : mfp_SingleBitQGt2 p)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (u₀ v₀ : ℝ) :
    ((1 - p) * u₀ + p * v₀) ^ 2 + (1 - u) * (p * (1 - p)) * (u₀ - v₀) ^ 2
      ≤ ((1 - p) * |u₀| ^ (2 - u) + p * |v₀| ^ (2 - u)) ^ (2 / (2 - u)) :=
  H u hu0 hu1 u₀ v₀


end StatMech.Probability
