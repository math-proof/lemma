/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexLocalIncomingPattern
    (omega : SixVertexArrows T) (v : T.Vertex) :
    SixVertexLocalIncomingPattern :=
  ![fkLoopWestIncoming omega v, fkLoopEastIncoming omega v,
    fkLoopSouthIncoming omega v, fkLoopNorthIncoming omega v]

end
end StatMech.FrontierD
