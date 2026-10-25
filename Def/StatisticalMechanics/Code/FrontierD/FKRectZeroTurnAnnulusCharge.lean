/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Instance.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingLeftRows
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Finset (Fin R.height) := by
  classical
  exact Finset.univ.filter fun y =>
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R, y) = C.1

end
end StatMech.FrontierD
