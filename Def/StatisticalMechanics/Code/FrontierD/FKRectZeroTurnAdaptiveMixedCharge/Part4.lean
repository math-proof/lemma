/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge.Part2


namespace StatMech.FrontierD

noncomputable section

def FKRectZeroTurnAdaptiveDualRouteSameSideUnique
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
    FKRectZeroTurnUsesAdaptiveDualRoute R omega C →
    FKRectZeroTurnUsesAdaptiveDualRoute R omega D →
    fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D → C = D


noncomputable def fkRectZeroTurnAdaptiveMixedCharge_of_dualRouteUniqueness
    (R : FKRectTorus) (omega : R.Configuration)
    (hdual : FKRectZeroTurnAdaptiveDualRouteSameSideUnique R omega) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  (fkRectZeroTurnAdaptiveMixedRouting R omega).toCharge R omega (by
    intro C D X hC hD hside
    exact hdual C D
      (fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr R omega C X hC)
      (fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr R omega D X hD)
      hside)


end
end StatMech.FrontierD
