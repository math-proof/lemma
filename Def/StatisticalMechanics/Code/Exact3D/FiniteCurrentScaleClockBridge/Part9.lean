/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part7


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  logError := h.logError
  mass_pos := h.mass_pos
  logError_negligible := h.logError_negligible
  log_mass_criticalDistanceScaleClock :=
    h.log_mass_criticalDistanceScaleClock

end FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := hcal.δ
  δ_pos := hcal.δ_pos
  δ_le_betaC := hcal.δ_le_betaC
  scaleBase := hcal.scaleBase
  scaleBase_gt_one := hcal.scaleBase_gt_one
  relevantEigenvalue := hcal.relevantEigenvalue
  relevantEigenvalue_gt_one := hcal.relevantEigenvalue_gt_one
  predictedExponent_eq := hcal.predictedExponent_eq
  clock := criticalDistanceScaleClock Ising3DModel hcal.relevantEigenvalue
  cLo := 1
  cLo_pos := zero_lt_one
  cHi := 1
  cHi_pos := zero_lt_one
  clock_annulus := by
    simpa [Ising3DModel] using
      criticalDistanceScaleClock_annulus_eventually
        Ising3DModel hcal.relevantEigenvalue_gt_one
  logError := hcal.logError
  mass_pos := hcal.mass_pos
  logError_negligible := hcal.logError_negligible
  log_mass_scaleClock := hcal.log_mass_criticalDistanceScaleClock

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

end Exact3D
end StatMech
