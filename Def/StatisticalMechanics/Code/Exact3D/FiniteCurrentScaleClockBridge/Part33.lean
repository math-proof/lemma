/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part23


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_annulusScaleClockAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockAverageError
      C I.massBridge havg

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
