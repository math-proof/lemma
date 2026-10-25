/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarsky
open Set Real Filter Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

def AizenmanBarskyInequalityPhysical (M : ℝ → ℝ → ℝ) (J : ℝ) : Prop :=
  ∀ β, 0 ≤ β → ∀ h, 0 < h →
    deriv (fun b => M b h) β ≤
      J * (M β h * deriv (fun t => M β t) h)


end Sharpness
end StatMech
