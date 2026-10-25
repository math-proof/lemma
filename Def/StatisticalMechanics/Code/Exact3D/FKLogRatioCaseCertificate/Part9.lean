/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part6


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimitVarying_of_eventuallyEq C fkMass modelMass H hMassEq)

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
