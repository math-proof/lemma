/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals


namespace StatMech

namespace Exact3D

namespace RatInterval

@[simp] theorem memQ_def (I : RatInterval) (q : ℚ) :
    I.MemQ q ↔ I.lower ≤ q ∧ q ≤ I.upper :=
  Iff.rfl

@[simp] theorem memR_def (I : RatInterval) (x : ℝ) :
    I.MemR x ↔ (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ) :=
  Iff.rfl


end RatInterval
end Exact3D
end StatMech
