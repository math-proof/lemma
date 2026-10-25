/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part5


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem MatrixMemQ.memR_coe {m n : ℕ} {A : Fin m → Fin n → ℚ}
    {I : IntervalMatrix m n} (hA : MatrixMemQ A I) :
    MatrixMem (fun i j => (A i j : ℝ)) I := by
  intro i j
  exact memR_of_memQ (hA i j)


end RatInterval
end Exact3D
end StatMech
