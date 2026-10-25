/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedDevelopedCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedDevelopedCertificate


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    fkRectZeroTurnMixedTouchedCertificate_of_geometricResidues
    (R : FKRectTorus)
    (hdisconnected : ∀ omega : R.Configuration,
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
    (hdual : ∀ omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    ∀ omega : R.Configuration,
      FKRectZeroTurnMixedTouchedCertificate R omega :=
  fun omega =>
    FKRectZeroTurnMixedTouchedCertificate.ofDisconnectedIncidence
      R omega (hdisconnected omega) (hdual omega)

end
end StatMech.FrontierD
