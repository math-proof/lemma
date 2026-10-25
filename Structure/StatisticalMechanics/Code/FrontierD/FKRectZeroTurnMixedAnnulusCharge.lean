/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge.Part2


namespace StatMech.FrontierD

noncomputable section

structure FKRectZeroTurnMixedAnnulusCharge
    (R : FKRectTorus) (omega : R.Configuration) where
  crossing : FKRectZeroTurnCutRemainderComponent R omega →
    FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega
  side : FKRectZeroTurnCutRemainderComponent R omega → Bool
  injective_pair : Function.Injective fun C => (crossing C, side C)


end
end StatMech.FrontierD
