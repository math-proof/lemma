/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part16


namespace StatMech

namespace Exact3D

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparison
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree I.massBridge hcmp

end FiniteCurrentMassBridgeInputs
end Exact3D
end StatMech
