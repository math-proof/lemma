/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part4
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

structure FKRectZeroTurnMixedTouchedCertificate
    (R : FKRectTorus) (omega : R.Configuration) where
  nonempty : ∀ C, (fkRectZeroTurnMixedTouchedCrossings R omega C).Nonempty
  sameSide_unique : ∀ C D X,
    X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C →
    X ∈ fkRectZeroTurnMixedTouchedCrossings R omega D →
    fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D → C = D


end
end StatMech.FrontierD
