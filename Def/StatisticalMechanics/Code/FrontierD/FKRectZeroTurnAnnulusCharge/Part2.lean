/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingFirstRow
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Fin R.height :=
  (fkRectRawPrimalCrossingLeftRows R omega C).min'
    (fkRectRawPrimalCrossingLeftRows_nonempty R omega C)


noncomputable def fkRectRawPrimalCrossingLastRow
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Fin R.height :=
  (fkRectRawPrimalCrossingLeftRows R omega C).max'
    (fkRectRawPrimalCrossingLeftRows_nonempty R omega C)

end
end StatMech.FrontierD
