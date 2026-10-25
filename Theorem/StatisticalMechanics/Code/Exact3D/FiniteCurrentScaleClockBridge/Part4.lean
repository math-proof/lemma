/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part7


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


theorem clockError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        (h.clock β -
            criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
      Ising3DModel h.clock h.relevantEigenvalue h.cLo h.cHi
      h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus))

set_option linter.style.longLine false in


theorem averageAccumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / h.clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue h.cLo
      h.cHi h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus)
      (by simpa [Ising3DModel] using h.accumulatedError_negligible))

end FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical
end Exact3D
end StatMech
