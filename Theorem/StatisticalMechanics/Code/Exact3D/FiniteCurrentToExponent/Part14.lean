/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part21


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget C hagree hpower)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw C hagree hasymp)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logAffine C hagree hlog)

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
