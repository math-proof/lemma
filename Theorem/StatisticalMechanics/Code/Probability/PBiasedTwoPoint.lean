/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BonamiTwoPoint
import Def.StatisticalMechanics.Code.Probability.PBiasedTwoPoint
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

theorem pbt_g_at_one (p q : ℝ) : pbt_g p q 1 = 1 := by
  unfold pbt_g; ring


theorem pbt_core_at_one (p q : ℝ) :
    pbt_g p q 1 ≤ ((1 - p) + p * (1:ℝ) ^ q) ^ (2 / q) := by
  rw [pbt_g_at_one, Real.one_rpow]
  have h : ((1 - p) + p * 1 : ℝ) = 1 := by ring
  rw [h, Real.one_rpow]


theorem pbt_OneVarCore_q_one (p : ℝ) : pbt_OneVarCore p 1 := by
  intro z _
  unfold pbt_g
  simp only [sub_self, zero_mul, add_zero, Real.rpow_one]
  rw [show (2:ℝ) / 1 = 2 by norm_num, Real.rpow_two]


end StatMech.Probability
