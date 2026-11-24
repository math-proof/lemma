module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part6


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

noncomputable def fkRectZeroTurnRemainderSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Bool :=
  decide (0 < (fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))).1)

end
end StatMech.FrontierD
