module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
public import Structure.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectZeroTurnUsesAdaptiveDualRoute
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Prop :=
  ¬ ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
    FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X

end
end StatMech.FrontierD
