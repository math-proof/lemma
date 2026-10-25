/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part4


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
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


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
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


noncomputable def freePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
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
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
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


noncomputable def freePositiveSubcriticalMassAnnulusScaleClockTerminalAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
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
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  terminalLog := hterm.terminalLog
  terminalLogLimit := hterm.terminalLogLimit
  terminalLog_tendsto := hterm.terminalLog_tendsto
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue hterm.cLo hterm.cHi
        hterm.relevantEigenvalue_gt_one hterm.cLo_pos hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_terminalAverageError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
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
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  terminalLog := hterm.terminalLog
  terminalLogBound := hterm.terminalLogBound
  terminalLog_eventually_abs_le := hterm.terminalLog_eventually_abs_le
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue hterm.cLo hterm.cHi
        hterm.relevantEigenvalue_gt_one hterm.cLo_pos hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_averageError := hterm.log_mass_boundedTerminalError

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockBoundedTerminalError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalError_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  cLo := havg.cLo
  cLo_pos := havg.cLo_pos
  cHi := havg.cHi
  cHi_pos := havg.cHi_pos
  clock_annulus := havg.clock_annulus
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogLimit havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus)
        (by simpa [Ising3DModel] using havg.terminalLog_tendsto)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_terminalAverageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass where
  δ := hann.δ
  δ_pos := hann.δ_pos
  δ_le_betaC := hann.δ_le_betaC
  scaleBase := hann.scaleBase
  scaleBase_gt_one := hann.scaleBase_gt_one
  relevantEigenvalue := hann.relevantEigenvalue
  relevantEigenvalue_gt_one := hann.relevantEigenvalue_gt_one
  predictedExponent_eq := hann.predictedExponent_eq
  clock := hann.clock
  logError := hann.logError
  mass_pos := hann.mass_pos
  clock_ratio_tendsto := by
    exact
      (tendsto_scaleClock_ratio_of_eventually_annulus
        Ising3DModel hann.clock hann.relevantEigenvalue hann.cLo hann.cHi
        hann.relevantEigenvalue_gt_one hann.cLo_pos hann.cHi_pos
        (by simpa [Ising3DModel] using hann.clock_annulus))
  logError_negligible := hann.logError_negligible
  log_mass_scaleClock := hann.log_mass_scaleClock

end Exact3D
end StatMech
