/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instDecidablePredFKRectRawPrimalHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    DecidablePred (FKRectRawHorizontalCrossingComponent R
      (fkRectForceCutClosed R omega)) :=
  Classical.decPred _


end
end StatMech.FrontierD
