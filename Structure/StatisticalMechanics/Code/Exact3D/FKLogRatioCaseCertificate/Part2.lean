/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part2


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


structure VaryingCertificate
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  Case : ℝ → Type*
  caseDecidableEq : ∀ epsilon, DecidableEq (Case epsilon)
  epsilonTable :
    ∀ epsilon, 0 < epsilon →
      @EpsilonTable C fkMass (Case epsilon)
        (caseDecidableEq epsilon) epsilon

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
