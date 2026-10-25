/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Set Real Filter Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

def AizenmanBarskyInequality (M : ℝ → ℝ → ℝ) (J : ℝ) : Prop :=
  ∀ β h, deriv (fun β => M β h) β ≤ J * (M β h * deriv (fun h => M β h) h)


def AizenmanBarskyPDI (M : ℝ → ℝ → ℝ) : Prop :=
  ∀ β h, M β h ≤
      h * deriv (fun h => M β h) h + (M β h) ^ 2 + β * (M β h * deriv (fun β => M β h) β)


end Sharpness
end StatMech
