/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part5
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in


noncomputable def FKRectZeroTurnMixedTouchedCertificate.toCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  FKRectZeroTurnMixedAnnulusCharge.ofCrossing R omega
    (fkRectZeroTurnSelectedMixedCrossing R omega certificate) (by
      intro C D hcross hside
      exact certificate.sameSide_unique C D
        (fkRectZeroTurnSelectedMixedCrossing R omega certificate C)
        (fkRectZeroTurnSelectedMixedCrossing_mem R omega certificate C)
        (hcross ▸
          fkRectZeroTurnSelectedMixedCrossing_mem R omega certificate D)
        hside)


end
end StatMech.FrontierD
