/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part3


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


theorem fkRectZeroTurnSelectedDualRightBoundaryContact_mem
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnSelectedDualRightBoundaryContact R omega C ∈
      fkRectZeroTurnDualRightBoundaryContacts R omega C :=
  (fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega C).choose_spec


end
end StatMech.FrontierD
