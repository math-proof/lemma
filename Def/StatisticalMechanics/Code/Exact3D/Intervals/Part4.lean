/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part3


namespace StatMech

namespace Exact3D

namespace RatInterval

def mul (I J : RatInterval) : RatInterval where
  lower := -(I.absUpper * J.absUpper)
  upper := I.absUpper * J.absUpper
  lower_le_upper := by
    exact neg_le_self (mul_nonneg I.absUpper_nonneg J.absUpper_nonneg)


def mulNonneg (I J : RatInterval) (hI : I.Nonnegative) (hJ : J.Nonnegative) :
    RatInterval where
  lower := I.lower * J.lower
  upper := I.upper * J.upper
  lower_le_upper :=
    mul_le_mul I.lower_le_upper J.lower_le_upper hJ (le_trans hI I.lower_le_upper)


end RatInterval
end Exact3D
end StatMech
