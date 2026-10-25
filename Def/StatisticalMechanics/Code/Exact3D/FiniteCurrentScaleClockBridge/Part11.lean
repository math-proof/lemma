/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part5


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hcal.δ
  δ_pos := hcal.δ_pos
  δ_le_betaC := hcal.δ_le_betaC
  scaleBase := hcal.scaleBase
  scaleBase_gt_one := hcal.scaleBase_gt_one
  relevantEigenvalue := hcal.relevantEigenvalue
  relevantEigenvalue_gt_one := hcal.relevantEigenvalue_gt_one
  predictedExponent_eq := hcal.predictedExponent_eq
  clock := criticalDistanceScaleClock Ising3DModel hcal.relevantEigenvalue
  clockError_negligible := by
    simp [Ising3DModel]
  logError := hcal.logError
  mass_pos := hcal.mass_pos
  logError_negligible := hcal.logError_negligible
  log_mass_scaleClock := hcal.log_mass_criticalDistanceScaleClock

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hclock.δ
  δ_pos := hclock.δ_pos
  δ_le_betaC := hclock.δ_le_betaC
  scaleBase := hclock.scaleBase
  scaleBase_gt_one := hclock.scaleBase_gt_one
  relevantEigenvalue := hclock.relevantEigenvalue
  relevantEigenvalue_gt_one := hclock.relevantEigenvalue_gt_one
  predictedExponent_eq := hclock.predictedExponent_eq
  clock := hclock.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio
        Ising3DModel hclock.clock hclock.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using hclock.clock_ratio_tendsto))
  logError := hclock.logError
  mass_pos := hclock.mass_pos
  logError_negligible := hclock.logError_negligible
  log_mass_scaleClock := hclock.log_mass_scaleClock

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hann.δ
  δ_pos := hann.δ_pos
  δ_le_betaC := hann.δ_le_betaC
  scaleBase := hann.scaleBase
  scaleBase_gt_one := hann.scaleBase_gt_one
  relevantEigenvalue := hann.relevantEigenvalue
  relevantEigenvalue_gt_one := hann.relevantEigenvalue_gt_one
  predictedExponent_eq := hann.predictedExponent_eq
  clock := hann.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel hann.clock hann.relevantEigenvalue hann.cLo hann.cHi
        hann.relevantEigenvalue_gt_one hann.cLo_pos hann.cHi_pos
        (by simpa [Ising3DModel] using hann.clock_annulus))
  logError := hann.logError
  mass_pos := hann.mass_pos
  logError_negligible := hann.logError_negligible
  log_mass_scaleClock := hann.log_mass_scaleClock

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass where
  δ := hcmp.δ
  δ_pos := hcmp.δ_pos
  δ_le_betaC := hcmp.δ_le_betaC
  scaleBase := hcmp.scaleBase
  scaleBase_gt_one := hcmp.scaleBase_gt_one
  relevantEigenvalue := hcmp.relevantEigenvalue
  relevantEigenvalue_gt_one := hcmp.relevantEigenvalue_gt_one
  predictedExponent_eq := hcmp.predictedExponent_eq
  clock := hcmp.clock
  logError := hcmp.logError
  mass_pos := hcmp.mass_pos
  clock_ratio_tendsto := hcmp.clock_ratio_tendsto
  logError_negligible := hcmp.logError_negligible
  log_mass_scaleClock := hcmp.log_mass_scaleClock

end Exact3D
end StatMech
