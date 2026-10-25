/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part18


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


theorem accumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_log_betaC_sub_of_clock_average
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible)
      (by simpa [Ising3DModel] using h.averageAccumulatedError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical
end Exact3D
end StatMech
