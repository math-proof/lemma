/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2


namespace StatMech.FrontierD

noncomputable section

abbrev FKRectZeroTurnCutRemainderComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  {C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) //
    C ∈ fkRectZeroTurnCutRemainderComponents R omega}


abbrev FKRectRawPrimalHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  {C : (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).ConnectedComponent //
    FKRectRawHorizontalCrossingComponent R
      (fkRectForceCutClosed R omega) C}

end
end StatMech.FrontierD
