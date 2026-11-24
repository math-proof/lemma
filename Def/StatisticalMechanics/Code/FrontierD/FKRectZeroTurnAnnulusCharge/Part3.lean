module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingExtremeRow
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : Fin R.height :=
  if side then fkRectRawPrimalCrossingFirstRow R omega C
  else fkRectRawPrimalCrossingLastRow R omega C

end
end StatMech.FrontierD
