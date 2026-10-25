/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part7
open StatMech.FrontierD


namespace ScratchLocalRetieC

@[simp] theorem blackDartOfStrandSlot_vertex
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) :
    (blackDartOfStrandSlot pairing slot).1.1 = slot.1 := by
  have h := congrArg Prod.fst
    ((fkMedialBlackDartEquivVertexBool T).apply_symm_apply
      (slot.1, blackSideIndexOfStrandSlot
        (fkMedialVertexParity slot.1) (pairing slot.1) slot.2))
  exact h

end ScratchLocalRetieC
