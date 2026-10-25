/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLocalIncomingPattern_count
    (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexLocalIncomingCount (sixVertexLocalIncomingPattern omega v) =
      omega.incomingCount v := by
  simp [sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexLocalIncomingPattern,
    SixVertexArrows.incomingCount, fkLoopWestIncoming,
    fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming]

theorem sixVertexLocalIncomingPattern_ice
    (omega : SixVertexArrows T) (homega : omega.IceRule)
    (v : T.Vertex) :
    (sixVertexLocalIncomingPattern omega v).Ice := by
  rw [SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalIncomingPattern_count]
  exact homega v

theorem sixVertexLocalIncomingPattern_isCType_iff
    (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexLocalIncomingPattern omega v).IsCType <->
      omega.IsCType v := by
  rfl

theorem sixVertexLocalPatternWeight_eq_localWeight
    (c : Real) (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexLocalPatternWeight c
        (sixVertexLocalIncomingPattern omega v) =
      omega.localWeight c v := by
  classical
  simp [sixVertexLocalPatternWeight, SixVertexLocalIncomingPattern.Ice,
    SixVertexLocalIncomingPattern.IsCType, SixVertexArrows.localWeight,
    sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexLocalIncomingPattern, SixVertexArrows.incomingCount,
    SixVertexArrows.IsCType, fkLoopWestIncoming, fkLoopEastIncoming,
    fkLoopSouthIncoming, fkLoopNorthIncoming]


end
end StatMech.FrontierD
