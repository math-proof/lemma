/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusSwitchFirst_involutive
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchFirst mask
        (sixVertexTorusSwitchFirst mask omega eta)
        (sixVertexTorusSwitchSecond mask omega eta) = omega := by
  apply SixVertexArrows.ext <;> funext v <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond] <;>
    split <;> simp_all


theorem sixVertexTorusSwitchSecond_involutive
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchSecond mask
        (sixVertexTorusSwitchFirst mask omega eta)
        (sixVertexTorusSwitchSecond mask omega eta) = eta := by
  apply SixVertexArrows.ext <;> funext v <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond] <;>
    split <;> simp_all


end
end StatMech.FrontierD
