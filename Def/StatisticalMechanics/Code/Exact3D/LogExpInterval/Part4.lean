/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LogExpBounds
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.LogExpInterval.Part3


namespace StatMech

namespace Exact3D

namespace RatInterval

def divNonnegPositive (I J : RatInterval)
    (hI : I.Nonnegative) (hJ : J.Positive) : RatInterval :=
  mulNonneg I (invPositive J hJ) hI (invPositive_nonnegative hJ)


end RatInterval
end Exact3D
end StatMech
