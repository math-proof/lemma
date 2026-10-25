/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega (certificate.toCharge R omega)

end
end StatMech.FrontierD
