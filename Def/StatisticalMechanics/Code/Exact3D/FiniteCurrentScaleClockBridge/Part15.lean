/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part7


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  terminalLog := hterm.terminalLog
  terminalLogBound := |hterm.terminalLogLimit| + 1
  terminalLog_eventually_abs_le := by
    exact
      eventually_abs_le_abs_limit_add_one_of_tendsto
        (by simpa [Ising3DModel] using hterm.terminalLog_tendsto)
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_boundedTerminalError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  logError := fun β => hterm.terminalLog β + hterm.accumulatedError β
  mass_pos := hterm.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub
        Ising3DModel hterm.terminalLog hterm.accumulatedError
        hterm.terminalLogBound
        (by simpa [Ising3DModel] using hterm.terminalLog_eventually_abs_le)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            hterm.terminalLog β + hterm.accumulatedError β :=
        hterm.log_mass_boundedTerminalError β hβ
      _ =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            (hterm.terminalLog β + hterm.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel hterm.clock hterm.relevantEigenvalue hterm.cLo
        hterm.cHi hterm.relevantEigenvalue_gt_one hterm.cLo_pos
        hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus))
  terminalLog := hterm.terminalLog
  terminalLogLimit := hterm.terminalLogLimit
  terminalLog_tendsto := hterm.terminalLog_tendsto
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_terminalError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel hterm.clock hterm.relevantEigenvalue hterm.cLo
        hterm.cHi hterm.relevantEigenvalue_gt_one hterm.cLo_pos
        hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus))
  terminalLog := hterm.terminalLog
  terminalLogBound := hterm.terminalLogBound
  terminalLog_eventually_abs_le := hterm.terminalLog_eventually_abs_le
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_boundedTerminalError := hterm.log_mass_boundedTerminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassBoundedTerminalError_of_annulusScaleClockBoundedTerminalError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalError_of_annulusScaleClockTerminalError
      C hmass hterm)

end Exact3D
end StatMech
