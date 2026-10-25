/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectZeroTurnPrimalTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalHorizontalCrossingComponent R omega) := by
  classical
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  exact Finset.univ.filter fun X =>
    ∃ x ∈ p.support,
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk x = X.1

end
end StatMech.FrontierD
