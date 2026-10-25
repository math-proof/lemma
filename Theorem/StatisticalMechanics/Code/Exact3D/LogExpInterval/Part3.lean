/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LogExpBounds
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.LogExpInterval.Part3


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem divPositive_memR {I J : RatInterval} (hJ : J.Positive)
    {x y : ℝ} (hx : I.MemR x) (hy : J.MemR y) :
    (divPositive I J hJ).MemR (x / y) := by
  simpa [divPositive, div_eq_mul_inv] using mul_memR hx (invPositive_memR hJ hy)


end RatInterval
end Exact3D
end StatMech
