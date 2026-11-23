/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge

@[expose] public section

namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def criticalDistanceScaleClock {ι : Type*}
    (M : CriticalModel ι) (relevantEigenvalue : ℝ) : ℝ → ℝ :=
  fun β => -Real.log (M.betaC - β) / Real.log relevantEigenvalue

end Exact3D
end StatMech
