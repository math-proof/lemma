/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LogExpBounds
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.LogExpInterval.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem invPositive_positive {I : RatInterval} (hI : I.Positive) :
    (invPositive I hI).Positive := by
  have hupper : (0 : ℚ) < I.upper := lt_of_lt_of_le hI I.lower_le_upper
  exact one_div_pos.mpr hupper


theorem invPositive_nonnegative {I : RatInterval} (hI : I.Positive) :
    (invPositive I hI).Nonnegative :=
  (invPositive_positive hI).le


theorem invPositive_memR {I : RatInterval} (hI : I.Positive)
    {x : ℝ} (hx : I.MemR x) :
    (invPositive I hI).MemR x⁻¹ := by
  have hIl : (0 : ℝ) < (I.lower : ℝ) := lower_pos_real_of_positive hI
  have hxpos : 0 < x := pos_of_positive_memR hI hx
  constructor
  · have hxu : x ≤ (I.upper : ℝ) := hx.2
    have h := one_div_le_one_div_of_le hxpos hxu
    simpa [invPositive, one_div] using h
  · have hxl : (I.lower : ℝ) ≤ x := hx.1
    have h := one_div_le_one_div_of_le hIl hxl
    simpa [invPositive, one_div] using h


end RatInterval
end Exact3D
end StatMech
