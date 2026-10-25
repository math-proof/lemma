/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part25


namespace StatMech

namespace Exact3D

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceScaleClock
      C hagree hcal)

end FiniteCurrentMassBridgeInputs
end Exact3D
end StatMech
