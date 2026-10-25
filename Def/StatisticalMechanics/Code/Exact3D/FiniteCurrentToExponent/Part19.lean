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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part11


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eq
      C hβeq T hfkMass)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree hmass hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eventuallyEq
      C hβeq T hfkMass)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_lengthEq
      C hmass hβeq T hisingLength
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    C hagree hmass hβeq hβc hselected T rfl

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
      C hmass hβeq T hisingLength
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementFKMassPowerLawTarget
    C hagree hmass hβeq hβc hselected T rfl

end Exact3D
end StatMech
