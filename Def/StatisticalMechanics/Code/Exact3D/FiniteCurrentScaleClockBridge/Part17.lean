/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part8


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel havg.clock havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus))
  terminalLog := havg.terminalLog
  terminalLogBound := havg.terminalLogBound
  terminalLog_eventually_abs_le := havg.terminalLog_eventually_abs_le
  accumulatedError := havg.accumulatedError
  averageAccumulatedError_negligible :=
    havg.averageAccumulatedError_negligible
  mass_pos := havg.mass_pos
  log_mass_averageError := havg.log_mass_averageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAverageError_of_annulusScaleClockAverageError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAverageError_of_annulusScaleClockAverageError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockTerminalError
      C hmass hterm)

end Exact3D
end StatMech
