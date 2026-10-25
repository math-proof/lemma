/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedDevelopedCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedDevelopedCertificate


namespace StatMech.FrontierD

noncomputable section

theorem
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_disconnectedIncidence
    (R : FKRectTorus) (omega : R.Configuration)
    (hdisconnected :
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
    (hdual : FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched
    R omega
      (FKRectZeroTurnMixedTouchedCertificate.ofDisconnectedIncidence
        R omega hdisconnected hdual)


end
end StatMech.FrontierD
