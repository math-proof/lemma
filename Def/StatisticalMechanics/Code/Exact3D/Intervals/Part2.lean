/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals


namespace StatMech

namespace Exact3D

namespace RatInterval

def point (q : ℚ) : RatInterval where
  lower := q
  upper := q
  lower_le_upper := le_rfl


def width (I : RatInterval) : ℚ :=
  I.upper - I.lower

end RatInterval
end Exact3D
end StatMech
