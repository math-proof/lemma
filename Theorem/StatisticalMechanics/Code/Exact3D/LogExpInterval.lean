/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LogExpBounds
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.LogExpInterval


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem point_positive {q : ℚ} (hq : 0 < q) : (point q).Positive := by
  simpa [Positive, point] using hq

theorem lower_pos_real_of_positive {I : RatInterval} (hI : I.Positive) :
    (0 : ℝ) < (I.lower : ℝ) := by
  exact_mod_cast hI


theorem pos_of_positive_memR {I : RatInterval} {x : ℝ}
    (hI : I.Positive) (hx : I.MemR x) :
    0 < x :=
  lt_of_lt_of_le (lower_pos_real_of_positive hI) hx.1


end RatInterval
end Exact3D
end StatMech
