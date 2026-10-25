/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part3
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectBlackBoundaryCycleDualComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent :=
  fkRectBlackBoundaryCyclePrimalComponent R
    (fkRectDualConfigurationEquiv R omega)
    (fkRectBlackBoundaryCycleDualEquiv R omega C)


end
end StatMech.FrontierD
