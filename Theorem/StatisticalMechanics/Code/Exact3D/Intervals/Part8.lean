/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part9


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem vectorAdd_nonnegative {n : ℕ} {I J : IntervalVector n}
    (hI : VectorNonnegative I) (hJ : VectorNonnegative J) :
    VectorNonnegative (vectorAdd I J) := by
  intro i
  exact add_nonnegative (hI i) (hJ i)


end RatInterval
end Exact3D
end StatMech
