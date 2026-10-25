/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part6


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
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
      (tendsto_terminal_add_error_div_log_betaC_sub
        Ising3DModel hterm.terminalLog hterm.accumulatedError
        hterm.terminalLogLimit
        (by simpa [Ising3DModel] using hterm.terminalLog_tendsto)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            hterm.terminalLog β + hterm.accumulatedError β :=
        hterm.log_mass_terminalError β hβ
      _ =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            (hterm.terminalLog β + hterm.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

end Exact3D
end StatMech
