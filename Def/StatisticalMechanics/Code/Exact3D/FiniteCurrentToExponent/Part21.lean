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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part13


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree I.massBridge hpower

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    C hagree I.massBridge hasymp

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logAffine
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    C hagree I.massBridge hlog

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree I.massBridge hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementExactPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree I.massBridge hβeq hβc hselected hexact

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLogAffine
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogAffineNearCritical
    C hagree I.massBridge hβeq hβc hselected hlog

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLogRatioLimit
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    C hagree I.massBridge hsand

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree I.massBridge hβeq hβc hselected hsand

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpper
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpperExists
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementFKMassPowerLawTarget
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    C hagree I.massBridge hβeq hβc hselected T hfkMass

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEq
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget_eventuallyEq
    C hagree I.massBridge hβeq hβc hselected T hfkMass

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCFKMassPowerLawTargetLengthEq
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            I.massBridge β) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_powerSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    C hagree I.massBridge hpow

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_subpowerPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassSubpowerPrefactorSandwich
    C hagree I.massBridge hsub

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_boundedPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassBoundedPrefactorSandwich
    C hagree I.massBridge hbounded

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakSandwich
    C hagree I.massBridge hconst

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooSandwich
    C hagree I.massBridge hIoo

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree I.massBridge hβc hlower hupper

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
