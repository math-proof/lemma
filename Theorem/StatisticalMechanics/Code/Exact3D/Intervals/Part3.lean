/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part3


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem absUpper_nonneg (I : RatInterval) : 0 ≤ I.absUpper := by
  by_cases h : 0 ≤ I.upper
  · exact le_trans h (le_max_right _ _)
  · have hupper : I.upper < 0 := lt_of_not_ge h
    have hlower : I.lower ≤ 0 := le_trans I.lower_le_upper hupper.le
    exact le_trans (neg_nonneg.mpr hlower) (le_max_left _ _)


theorem absUpper_point (q : ℚ) : (point q).absUpper = |q| := by
  rw [abs_eq_max_neg]
  simp [absUpper, point, max_comm]


end RatInterval
end Exact3D
end StatMech
