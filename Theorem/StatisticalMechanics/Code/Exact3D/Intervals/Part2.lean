/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem width_nonneg (I : RatInterval) : 0 ≤ I.width := by
  exact sub_nonneg.mpr I.lower_le_upper


end RatInterval
end Exact3D
end StatMech
