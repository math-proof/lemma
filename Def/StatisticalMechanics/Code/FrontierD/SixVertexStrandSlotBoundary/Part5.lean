/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part4


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkColoredLayeredStrandSlotBoundaryPerm
    {T : EvenTorus} (pairing : Bool -> FKMedialLoopPairing T) :
    Equiv.Perm (FKLayeredStrandSlot T) where
  toFun slot :=
    (slot.1, fkColoredStrandSlotBoundaryPerm (pairing slot.1) slot.2)
  invFun slot :=
    (slot.1,
      (fkColoredStrandSlotBoundaryPerm (pairing slot.1)).symm slot.2)
  left_inv slot := by simp
  right_inv slot := by simp

end
end StatMech.FrontierD
