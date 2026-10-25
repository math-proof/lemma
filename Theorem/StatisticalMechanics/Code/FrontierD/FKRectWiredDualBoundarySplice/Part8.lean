/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectZeroTurnDualRightBoundaryContacts
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (y : Fin R.height) :
    y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ↔
      (fkRectRightColumn R, y) ∈
        (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support := by
  classical
  simp [fkRectZeroTurnDualRightBoundaryContacts]


theorem fkRectZeroTurnDualRightBoundaryContacts_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectZeroTurnDualRightBoundaryContacts R omega C).Nonempty := by
  have hwind : (fkRectWalkWinding R
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C)).1 ≠ 0 := by
    rw [fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding]
    exact fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  obtain ⟨y, hy⟩ :=
    exists_fkRectRightBoundaryVertex_mem_support_of_winding R
      (fkRectDualConfigurationEquiv R omega)
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C) hwind
  exact ⟨y,
    (mem_fkRectZeroTurnDualRightBoundaryContacts R omega C y).2 hy⟩


end
end StatMech.FrontierD
