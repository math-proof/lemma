/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

theorem geometricHalfTailWeight_nonneg (n : ℕ) :
    0 ≤ geometricHalfTailWeight n := by
  unfold geometricHalfTailWeight
  exact pow_nonneg (by norm_num) _


theorem geometricHalfTailWeight_summable :
    Summable geometricHalfTailWeight := by
  have hgeom :
      Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
    summable_geometric_of_abs_lt_one (by norm_num)
  refine (hgeom.mul_left ((1 : ℝ) / 2)).congr ?_
  intro n
  unfold geometricHalfTailWeight
  rw [pow_succ']


theorem geometricHalfTailWeight_tsum_eq_one :
    (∑' n : ℕ, geometricHalfTailWeight n) = 1 := by
  have hgeom_tsum :
      (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 := by
    rw [tsum_geometric_of_abs_lt_one (by norm_num :
      |((1 : ℝ) / 2)| < 1)]
    norm_num
  calc
    (∑' n : ℕ, geometricHalfTailWeight n) =
        ∑' n : ℕ, ((1 : ℝ) / 2) * (((1 : ℝ) / 2) ^ n) := by
      refine tsum_congr ?_
      intro n
      unfold geometricHalfTailWeight
      rw [pow_succ']
    _ = ((1 : ℝ) / 2) *
        (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) := by
      rw [tsum_mul_left]
    _ = 1 := by
      rw [hgeom_tsum]
      norm_num


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
