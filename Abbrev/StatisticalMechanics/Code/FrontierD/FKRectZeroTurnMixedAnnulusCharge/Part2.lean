/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
import Instance.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

abbrev FKRectRawPrimalWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  FKRectRawPrimalHorizontalCrossingComponent R omega ⊕
    FKRectRawWiredDualHorizontalCrossingComponent R omega


end
end StatMech.FrontierD
