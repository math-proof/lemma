/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech

namespace Exact3D

structure RatInterval where
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper

end Exact3D
end StatMech
