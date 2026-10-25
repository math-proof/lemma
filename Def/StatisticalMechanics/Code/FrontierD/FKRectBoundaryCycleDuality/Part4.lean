/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part4
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDualClusterBoundaryCycleWindingSum
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) : Int × Int := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      if fkRectBlackBoundaryCycleDualComponent R omega C = L then
        fkRectBlackBoundaryCycleWinding R omega C else 0

end
end StatMech.FrontierD
