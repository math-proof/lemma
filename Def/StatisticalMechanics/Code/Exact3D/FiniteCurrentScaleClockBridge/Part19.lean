/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part9


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalAverageError_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
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
  terminalLogLimit := hterm.terminalLogLimit
  terminalLog_tendsto := hterm.terminalLog_tendsto
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using hterm.clockError_negligible)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_terminalAverageError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_boundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
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
  terminalLogBound := hterm.terminalLogBound
  terminalLog_eventually_abs_le := hterm.terminalLog_eventually_abs_le
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using hterm.clockError_negligible)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_averageError := hterm.log_mass_boundedTerminalError

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassAverageError_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAverageError_of_boundedTerminalError
    C hmass
    (freePositiveSubcriticalMassBoundedTerminalError_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalAverageError_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
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
  terminalLogLimit := havg.terminalLogLimit
  terminalLog_tendsto := havg.terminalLog_tendsto
  accumulatedError := havg.accumulatedError
  averageAccumulatedError_negligible :=
    havg.averageAccumulatedError_negligible
  mass_pos := havg.mass_pos
  log_mass_terminalAverageError := havg.log_mass_terminalAverageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassTerminalAverageError_of_annulusScaleClockTerminalAverageError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockTerminalAverageError_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
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
  clockError_negligible := havg.clockError_negligible
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogLimit havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
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


noncomputable def freePositiveSubcriticalMassTerminalError_of_terminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
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
  clockError_negligible := havg.clockError_negligible
  terminalLog := havg.terminalLog
  terminalLogLimit := havg.terminalLogLimit
  terminalLog_tendsto := havg.terminalLog_tendsto
  accumulatedError := havg.accumulatedError
  accumulatedError_negligible := by
    exact
      (tendsto_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.accumulatedError
        havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  mass_pos := havg.mass_pos
  log_mass_terminalError := havg.log_mass_terminalAverageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_terminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
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
  clockError_negligible := havg.clockError_negligible
  terminalLog := havg.terminalLog
  terminalLogBound := |havg.terminalLogLimit| + 1
  terminalLog_eventually_abs_le := by
    exact
      eventually_abs_le_abs_limit_add_one_of_tendsto
        (by simpa [Ising3DModel] using havg.terminalLog_tendsto)
  accumulatedError := havg.accumulatedError
  averageAccumulatedError_negligible :=
    havg.averageAccumulatedError_negligible
  mass_pos := havg.mass_pos
  log_mass_averageError := havg.log_mass_terminalAverageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
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
  clockError_negligible := havg.clockError_negligible
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogBound havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by simpa [Ising3DModel] using havg.terminalLog_eventually_abs_le)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_averageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_averageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
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
  clockError_negligible := havg.clockError_negligible
  terminalLog := havg.terminalLog
  terminalLogBound := havg.terminalLogBound
  terminalLog_eventually_abs_le := havg.terminalLog_eventually_abs_le
  accumulatedError := havg.accumulatedError
  accumulatedError_negligible := by
    exact
      (tendsto_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.accumulatedError
        havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  mass_pos := havg.mass_pos
  log_mass_boundedTerminalError := havg.log_mass_averageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass where
  δ := hclock.δ
  δ_pos := hclock.δ_pos
  δ_le_betaC := hclock.δ_le_betaC
  mass_pos := hclock.mass_pos
  log_mass_ratio_tendsto := by
    let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
    have hlog :
        ∀ᶠ β in L,
          Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
            -(Real.log hclock.scaleBase) * hclock.clock β +
              hclock.logError β := by
      filter_upwards
        [Ioo_mem_nhdsLT
          (show Ising.betaC 3 - hclock.δ < Ising.betaC 3 by
            linarith [hclock.δ_pos])]
        with β hβ
      exact hclock.log_mass_scaleClock β hβ
    have hratio :=
      tendsto_log_mass_div_log_betaC_sub_of_scaleClock
        Ising3DModel
        (freeSelectedPositiveSubcriticalMass hmass)
        hclock.clock hclock.logError
        hclock.scaleBase hclock.relevantEigenvalue
        (by
          simpa [L, Ising3DModel] using hclock.clock_ratio_tendsto)
        (by
          simpa [L, Ising3DModel] using hclock.logError_negligible)
        (by
          simpa [L, Ising3DModel] using hlog)
    simpa [hclock.predictedExponent_eq] using hratio

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C hmass hclock)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C hmass hclock)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C hmass hclock)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_scaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree I.massBridge hclock

end FiniteCurrentMassBridgeInputs
end Exact3D
end StatMech
