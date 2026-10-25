/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part7


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem VectorMemQ.memR_coe {n : ℕ} {x : Fin n → ℚ} {I : IntervalVector n}
    (hx : VectorMemQ x I) :
    VectorMem (fun i => (x i : ℝ)) I := by
  intro i
  exact memR_of_memQ (hx i)


end RatInterval
end Exact3D
end StatMech
