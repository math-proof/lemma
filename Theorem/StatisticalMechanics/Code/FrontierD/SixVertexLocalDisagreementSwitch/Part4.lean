/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part5
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRectangleLocalIncomingPattern_count
    (omega : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    sixVertexLocalIncomingCount
        (sixVertexRectangleLocalIncomingPattern omega v) =
      omega.incomingCount v := by
  simp [sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexRectangleLocalIncomingPattern,
    SixVertexRectangleArrows.incomingCount]

theorem sixVertexRectangleLocalIncomingPattern_ice
    (omega : SixVertexRectangleArrows N M) (homega : omega.IceRule)
    (v : Fin N × Fin M) :
    (sixVertexRectangleLocalIncomingPattern omega v).Ice := by
  rw [SixVertexLocalIncomingPattern.Ice,
    sixVertexRectangleLocalIncomingPattern_count]
  exact homega v

theorem sixVertexRectangleLocalIncomingPattern_isCType_iff
    (omega : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    (sixVertexRectangleLocalIncomingPattern omega v).IsCType <->
      omega.IsCType v := by
  rfl

theorem sixVertexRectangleLocalPatternWeight_eq_localWeight
    (c : Real) (omega : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) :
    sixVertexLocalPatternWeight c
        (sixVertexRectangleLocalIncomingPattern omega v) =
      omega.localWeight c v := by
  classical
  simp [sixVertexLocalPatternWeight, SixVertexLocalIncomingPattern.Ice,
    SixVertexLocalIncomingPattern.IsCType,
    sixVertexLocalIncomingCount, Fin.sum_univ_four,
    sixVertexRectangleLocalIncomingPattern,
    SixVertexRectangleArrows.localWeight,
    SixVertexRectangleArrows.incomingCount,
    SixVertexRectangleArrows.IsCType]


end
end StatMech.FrontierD
