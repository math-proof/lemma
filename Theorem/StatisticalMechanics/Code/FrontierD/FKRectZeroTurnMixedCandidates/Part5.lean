/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part5
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnSelectedMixedCrossing_mem
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnSelectedMixedCrossing R omega certificate C ∈
      fkRectZeroTurnMixedTouchedCrossings R omega C :=
  (certificate.nonempty C).choose_spec

end
end StatMech.FrontierD
