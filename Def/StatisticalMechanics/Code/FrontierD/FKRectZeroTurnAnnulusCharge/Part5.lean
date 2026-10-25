/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part4


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingExtremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : FKMedialDart R.medialTorus :=
  fkRectMedialDartAtPrimalVertex R
    (fkRectLeftColumn R,
      fkRectRawPrimalCrossingExtremeRow R omega C side)

end
end StatMech.FrontierD
