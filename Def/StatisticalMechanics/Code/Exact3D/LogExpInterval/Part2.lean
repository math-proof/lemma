/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LogExpBounds
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.LogExpInterval


namespace StatMech

namespace Exact3D

namespace RatInterval

def invPositive (I : RatInterval) (hI : I.Positive) : RatInterval where
  lower := 1 / I.upper
  upper := 1 / I.lower
  lower_le_upper := by
    have hl : (0 : ℚ) < I.lower := hI
    exact one_div_le_one_div_of_le hl I.lower_le_upper


end RatInterval
end Exact3D
end StatMech
