/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectZeroTurnDualRightBoundaryContacts
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (Fin R.height) := by
  classical
  exact Finset.univ.filter fun y =>
    (fkRectRightColumn R, y) ∈
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support

end
end StatMech.FrontierD
