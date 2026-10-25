/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexMarkedSectorConfigurationEquivRowCycle
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    SixVertexMarkedSectorConfiguration T sector ≃
      SixVertexMarkedSectorRowCycle T sector where
  toFun omega :=
    ⟨svTorusRowsEquiv T omega.1,
      (sixVertexIceRule_iff_horizontalRowTransitions omega.1).mp omega.2.1,
      omega.2.2⟩
  invFun rows :=
    ⟨(svTorusRowsEquiv T).symm rows.1,
      (sixVertexIceRule_iff_horizontalRowTransitions
        ((svTorusRowsEquiv T).symm rows.1)).mpr (by
          simpa using rows.2.1),
      by simpa [svTorusVerticalRows] using rows.2.2⟩
  left_inv omega := by
    apply Subtype.ext
    exact (svTorusRowsEquiv T).symm_apply_apply omega.1
  right_inv rows := by
    apply Subtype.ext
    exact (svTorusRowsEquiv T).apply_symm_apply rows.1


def sixVertexMarkedSectorRowCycleTotalC
    {T : EvenTorus} {sector : Fin (T.width + 1)}
    (rows : SixVertexMarkedSectorRowCycle T sector) : Nat :=
  ∑ j, sixVertexRowDistance
    (rows.1.2 (SixVertexArrows.cyclicPred T.height_pos j))
    (rows.1.2 j)

end
end StatMech.FrontierD
