/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part7
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusLocalIncomingPattern_pairSwitch
    (mask omega eta : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst mask omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond mask omega eta) v) =
      sixVertexLocalSwapMask
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)
        (sixVertexTorusLocalSwitchMask mask v) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [sixVertexLocalIncomingPattern, sixVertexTorusSwitchFirst,
      sixVertexTorusSwitchSecond, sixVertexTorusLocalSwitchMask,
      sixVertexLocalSwapMask, fkLoopWestIncoming, fkLoopEastIncoming,
      fkLoopSouthIncoming, fkLoopNorthIncoming] <;> split <;> simp_all

end
end StatMech.FrontierD
