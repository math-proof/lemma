/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part8


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem VectorAbsSum_nonneg {n : ℕ} (I : IntervalVector n) :
    0 ≤ VectorAbsSum I := by
  unfold VectorAbsSum
  exact Finset.sum_nonneg fun i _ => (I i).absUpper_nonneg


theorem VectorAbsSum_nonneg_real {n : ℕ} (I : IntervalVector n) :
    0 ≤ (VectorAbsSum I : ℝ) := by
  exact_mod_cast VectorAbsSum_nonneg I


theorem VectorAbsSum_le_of_absUpper_le {n : ℕ}
    {I J : IntervalVector n}
    (h : ∀ i, (I i).absUpper ≤ (J i).absUpper) :
    VectorAbsSum I ≤ VectorAbsSum J := by
  unfold VectorAbsSum
  exact Finset.sum_le_sum fun i _ => h i


end RatInterval
end Exact3D
end StatMech
