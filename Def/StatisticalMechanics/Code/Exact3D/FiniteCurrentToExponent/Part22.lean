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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part19


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_asymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_asymptoticPowerLaw
      C I.massBridge hasymp

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_fkPCSelectedAgreementLogRatioLimit
      C I.massBridge hβeq hβc hselected hratio

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
