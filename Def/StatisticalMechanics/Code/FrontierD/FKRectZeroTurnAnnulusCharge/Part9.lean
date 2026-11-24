module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part8


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

def FKRectZeroTurnCrossingMatches
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Prop :=
  fkRectRawPrimalCrossingTorusComponent R omega X =
    fkRectZeroTurnRemainderPrimalComponent R omega C


end
end StatMech.FrontierD
