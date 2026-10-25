/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part8


namespace StatMech

namespace Exact3D

namespace RatInterval

def pointVector {n : ℕ} (x : Fin n → ℚ) : IntervalVector n :=
  fun i => point (x i)


def pointMatrix {m n : ℕ} (A : Fin m → Fin n → ℚ) : IntervalMatrix m n :=
  fun i j => point (A i j)

end RatInterval
end Exact3D
end StatMech
