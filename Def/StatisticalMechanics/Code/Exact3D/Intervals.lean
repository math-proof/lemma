/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.StatisticalMechanics.Code.Exact3D.Intervals


namespace StatMech

namespace Exact3D

namespace RatInterval

def MemQ (I : RatInterval) (q : ℚ) : Prop :=
  I.lower ≤ q ∧ q ≤ I.upper


def MemR (I : RatInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

end RatInterval
end Exact3D
end StatMech
