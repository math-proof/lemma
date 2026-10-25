/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instDecidablePredFKRectRawWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    DecidablePred (FKRectRawHorizontalCrossingComponent R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R omega))) :=
  Classical.decPred _


end
end StatMech.FrontierD
