/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part10


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in

theorem clock_ratio_tendsto
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        h.clock β / (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds ((Real.log h.relevantEigenvalue)⁻¹)) := by
  exact
    (tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
      Ising3DModel h.clock h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical
end Exact3D
end StatMech
