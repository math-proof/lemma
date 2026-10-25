/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectZeroTurnPrimalTouchedCrossingsInMixed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) := by
  classical
  exact (fkRectZeroTurnPrimalTouchedCrossings R omega C).image Sum.inl


noncomputable def fkRectZeroTurnDualTouchedCrossingsInMixed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) := by
  classical
  exact (fkRectZeroTurnDualTouchedCrossings R omega C).image Sum.inr


noncomputable def fkRectZeroTurnMixedTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) := by
  classical
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  if FKRectWalkAvoidsRowSeam R p then
    exact fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C
  else
    exact fkRectZeroTurnDualTouchedCrossingsInMixed R omega C


def FKRectZeroTurnUsesPrimalTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Prop :=
  FKRectWalkAvoidsRowSeam R
    (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))

end
end StatMech.FrontierD
